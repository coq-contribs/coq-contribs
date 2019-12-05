#!/usr/bin/env python3
import sys, re, os
from collections import defaultdict

# Usage: ./convert.py logfile
# Uses the warnings in logfile to locate compatibility notation warnings,
# then search and replace to use the correct notations.

if __name__ == '__main__':
    if len(sys.argv) <= 1:
        print("Add a log file to the command line", file=sys.stderr)
        exit (-1)
    logfile = sys.argv[1]
    # process warnings one by one
    repl = defaultdict(list)
    with open(logfile) as fin:
        while True:
            # search for a line of the form "File ..." followed by another
            # line of the form "Warning ..."
            line = fin.readline()
            if not line:
                break
            warning1 = re.search(r'File "([^"]*)", line ([0-9]*), characters ([0-9]*)-([0-9]*):', line)
            if not warning1:
                continue
            line = fin.readline ()
            # the "[compatibility-notation,deprecated]" part may be rejected
            # to a third line
            warning2 = re.search(r'Warning: ([^ ]*)\s+is\s+([^ ]*)(?:\n|\s*.compatibility-notation,deprecated.)', line)
            if not warning2:
                continue
            filename = warning1.group(1)
            line = warning1.group(2)
            old_notation = warning2.group(1)
            new_notation = warning2.group(2)
            print('File {} at line {}: {} should be written {}.'
                    .format(filename, line,old_notation,new_notation))

            # line numbers are 1-indexed in Coq, 0-indexed in python
            # character numbers are 0-indexed in both
            numline = int(line) - 1
            last_char = int(warning1.group(4))
            repl[filename].append((numline, old_notation, new_notation, last_char))

    for filename, l in repl.items():

        # for each file, we correct warnings line by line
        with open(filename, 'r') as vfile:
            data = vfile.readlines()

    
        for numline, old_notation, new_notation, last_char in l:
            # When notation appears in multiline tactics, the line reported is
            # the starting line of the tactic, thus the notation may
            # be on a following line. In this case, though, the last character
            # is greater than the length of the line, so we can detect it.
            # When this occurs, we try to
            # find the corresponding notation in the following lines. Cannot
            # blindly rely on nb_sub = 0 to detect such cases, since, for some
            # reason, some warnings appear twice (and here we perform as many
            # substitutions as we can, we could try to perform at most one for
            # each warning to be more precise).
            while True:
                data[numline], nb_sub = re.subn(r'\b{}\b'.format(old_notation),
                                                new_notation, data[numline])

                if nb_sub > 0 or last_char < len(data[numline]):
                    break
                last_char -= len(data[numline])
                numline += 1
                assert (numline < len(data))

        with open(filename, 'w') as vfile:
            vfile.writelines( data )
