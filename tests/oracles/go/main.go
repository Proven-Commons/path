// The Go oracle: path.Clean and path.Join from the standard library.
//
// It reads requests on standard input, one per line, as `path serve`
// does (see the header of Main.lean):
//
//	clean HEX      prints  OK and the hex of path.Clean
//	join HEX...    prints  OK and the hex of path.Join
//
// A path is the hex of its octets, and the empty path is `-`. Anything
// else prints `n/a`.
package main

import (
	"bufio"
	"encoding/hex"
	"fmt"
	"os"
	"path"
	"strings"
)

func field(f string) (string, bool) {
	if f == "-" {
		return "", true
	}
	b, err := hex.DecodeString(f)
	if err != nil || f == "" {
		return "", false
	}
	return string(b), true
}

func out(s string) string {
	if s == "" {
		return "-"
	}
	return hex.EncodeToString([]byte(s))
}

func answer(line string) string {
	fs := strings.Split(line, " ")
	switch {
	case fs[0] == "clean" && len(fs) == 2:
		p, ok := field(fs[1])
		if !ok {
			return "n/a"
		}
		return "OK " + out(path.Clean(p))
	case fs[0] == "join":
		var es []string
		for _, f := range fs[1:] {
			e, ok := field(f)
			if !ok {
				return "n/a"
			}
			es = append(es, e)
		}
		return "OK " + out(path.Join(es...))
	}
	return "n/a"
}

func main() {
	in := bufio.NewReaderSize(os.Stdin, 1<<20)
	w := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer w.Flush()
	for {
		line, err := in.ReadString('\n')
		if line == "" && err != nil {
			return
		}
		line = strings.TrimSuffix(strings.TrimSuffix(line, "\n"), "\r")
		fmt.Fprintln(w, answer(line))
	}
}
