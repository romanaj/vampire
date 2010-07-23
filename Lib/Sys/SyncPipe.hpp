/**
 * @file SyncPipe.hpp
 * Defines class SyncPipe.
 */

#ifndef __SyncPipe__
#define __SyncPipe__

#include <fstream>

#include "Forwards.hpp"

#include "Lib/fdstream.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Portability.hpp"

#include "Semaphore.hpp"

namespace Lib {
namespace Sys {

#if COMPILER_MSVC

class SyncPipe {
public:
  bool isReading() const { NOT_IMPLEMENTED; }
  bool canRead() const { NOT_IMPLEMENTED; }
  void acquireRead() { NOT_IMPLEMENTED; }
  void releaseRead() { NOT_IMPLEMENTED; }
  void neverRead() { NOT_IMPLEMENTED; }
  bool isWriting() const { NOT_IMPLEMENTED; }
  bool canWrite() const { NOT_IMPLEMENTED; }
  void acquireWrite() { NOT_IMPLEMENTED; }
  void releaseWrite() { NOT_IMPLEMENTED; }
  void neverWrite() { NOT_IMPLEMENTED; }
  void releasePriviledges() { NOT_IMPLEMENTED; }
  istream& in() { NOT_IMPLEMENTED; }
  ostream& out() { NOT_IMPLEMENTED; }
};

#else

class SyncPipe {
public:
  SyncPipe();
  ~SyncPipe();

  /** Return true iff the current object has acquired the read priviledge */
  bool isReading() const { return _isReading; }
  /** Return true iff the current object can acquire read priviledges */
  bool canRead() const { return _istream; }

  void acquireRead();
  void releaseRead();
  void neverRead();

  /** Return true iff the current object has acquired the write priviledge */
  bool isWriting() const { return _isWriting; }
  /** Return true iff the current object can acquire write priviledges */
  bool canWrite() const { return _ostream; }

  void acquireWrite();
  void releaseWrite();
  void neverWrite();

  void releasePriviledges();

  /**
   * If we have read privilidges, return reference to an istream object
   */
  istream& in()
  {
    ASS(_istream);
    ASS(isReading());
    if(!isReading()) {
      INVALID_OPERATION("Unallowed read from pipe.");
    }
    return *_istream;
  }

  /**
   * If we have write privilidges, return reference to an ostream object
   */
  ostream& out()
  {
    ASS(_ostream);
    ASS(isWriting());
    if(!isWriting()) {
      INVALID_OPERATION("Unallowed write to pipe.");
    }
    return *_ostream;
  }

private:
  SyncPipe(const SyncPipe&); //private and undefined
  const SyncPipe& operator=(const SyncPipe&); //private and undefined

  /** Contains pointer to input stream reading from the pipe, or 0 if
   * @b neverRead has been called */
  fdstream *_istream;
  /** Contains pointer to output stream writing to the pipe, or 0 if
   * @b neverWrite has been called */
  fdstream *_ostream;

  int _readDescriptor;
  int _writeDescriptor;
  bool _isReading;
  bool _isWriting;

  /**
   * Semaphore object with three semaphores. The first (number 0)
   * controls reading, the second one controls writing, and the third
   * one contains the value of the read-ahead byte from the pipe, or
   * 256 if there is not any.
   *
   * When the semaphore value is one, anyone can acquire a priviledge,
   * when it is zero, the acquire function will wait until it
   * increases.
   */
  Semaphore _syncSemaphore;

  static void postForkChildHadler();
  static void terminationHadler();
  static void ensureEventHandlersInstalled();

  typedef List<SyncPipe*> PipeList;

  static PipeList* s_instances;
};

#endif //COMPILER_MSVC

}
}

#endif // __SyncPipe__
