"""Text for the developer's log.

The log is written by jobs that hold a token, and GitHub's runner reads commands in it: `::command::`
at the start of a line, and the legacy `##[command]` anywhere in one. It may look for them with
culture-sensitive comparisons, which skip invisible characters. Every message that carries text from
the developer's repository or export goes through log_line.
"""
import unicodedata


def log_line(s: str) -> str:
    """`s` as one line of printable ASCII in which no workflow command can be read.

    Control and format characters (Unicode categories Cc and Cf: line breaks, zero-width, bidi and
    other invisible characters) are removed. Any other character outside printable ASCII is escaped
    visibly, as ascii() escapes it (\\xab, \\u2028), and a backslash is doubled. Then `::` and `##`
    are broken with a space until neither is left.
    """
    out = []
    for c in str(s):
        if unicodedata.category(c) in ('Cc', 'Cf'):
            continue
        n = ord(c)
        if c == '\\':
            out.append('\\\\')
        elif 0x20 <= n <= 0x7e:
            out.append(c)
        elif n <= 0xff:
            out.append('\\x%02x' % n)
        elif n <= 0xffff:
            out.append('\\u%04x' % n)
        else:
            out.append('\\U%08x' % n)
    line = ''.join(out)
    while '::' in line or '##' in line:
        line = line.replace('::', ': :').replace('##', '# #')
    return line
