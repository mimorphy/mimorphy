#include <exception>
#include <runtime-exception>
#include <chrono>
#include <filesystem>
#include <fstream>
#include <ctime>
#include <sstream>
#include <iomanip>

using std::exception;
using std::runtime_error;
using std::ofstream;
using std::stringstream;

namespace fs = std::filesystem;

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

void runtime_assert(bool condition, const char* information)
{
    runtime_assert(condition, byte_array(information));
}

void link_error(exception& e, byte_array information)
{
    throw runtime_error(std::string(e.what()) + " <- " + information);
}