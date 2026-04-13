#include "basic"
#include <exception>
#include <runtime-exception>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <ctime>
#include <shared_mutex>
#include <sstream>
#include <iomanip>
#include <stdexcept>
#include <vector>

using std::vector;
using std::exception;
using std::runtime_error;
using std::ofstream;
using std::stringstream;
using std::shared_mutex;
using std::shared_lock;

namespace fs = std::filesystem;

static vector<vector<byte_array>> exception_pools{{} };
static shared_mutex exception_pool_mutex{};

static byte_array get_current_time() {
    auto now = std::chrono::system_clock::now();
    auto time_t = std::chrono::system_clock::to_time_t(now);
    
    std::tm local_tm;
    localtime_r(&time_t, &local_tm);  // 线程安全版本
    
    stringstream ss;
    ss << std::put_time(&local_tm, "%Y-%m-%d %H:%M:%S");
    return byte_array(ss.str().c_str());
}

void runtime_assert(bool condition, byte_array information)
{
    if (condition) {
        return;
    }
    
    auto now = std::chrono::system_clock::now();
    auto time_t = std::chrono::system_clock::to_time_t(now);
    std::tm local_tm;
    localtime_r(&time_t, &local_tm);
    
    fs::path current_path = fs::current_path();
    
    stringstream filename_ss;
    filename_ss << current_path.string() << "/ErrorReport-" 
                << (local_tm.tm_year + 1900) << "-"
                << (local_tm.tm_mon + 1) << "-"
                << local_tm.tm_mday << ".txt";
    
    ofstream file(filename_ss.str(), std::ios::app);
    if (file.is_open()) {
        file << "\n[" << get_current_time() << "]: " << information;
    }
    file.close();

    throw runtime_error(information);
}

void runtime_assert(bool condition, const char* information, sizevalue index)
{
    if (condition) {
        return;
    }
    shared_lock<shared_mutex> lock(exception_pool_mutex);
    exception_pools[index].push_back(information);
}

void link_error(exception& e, byte_array information)
{
    throw runtime_error(std::string(e.what()) + " <- " + information);
}

sizevalue register_exception_pool()
{
    shared_lock<shared_mutex> lock(exception_pool_mutex);
    exception_pools.push_back({});
    return exception_pools.size() - 1;
}

void unregister_exception_pool(sizevalue index)
{
    shared_lock<shared_mutex> lock(exception_pool_mutex);
    exception_pools.erase(exception_pools.begin() + index);
}

sizevalue length_of_exception_pool(sizevalue index)
{
    shared_lock<shared_mutex> lock(exception_pool_mutex);
    return exception_pools[index].size();
}

const char* information_of_exception_pool_by_index(sizevalue index_of_pool, sizevalue index_of_information)
{
    shared_lock<shared_mutex> lock(exception_pool_mutex);
    return exception_pools[index_of_pool][index_of_information].c_str();
}

void clear_excpetion_pool(sizevalue index)
{
    shared_lock<shared_mutex> lock(exception_pool_mutex);
    exception_pools[index].clear();
}