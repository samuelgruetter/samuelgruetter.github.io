import csv
import re
from datetime import datetime

# The "Extra" field has to contain a line of the form
# Citation Key: PaperName_ConferenceAbbreviationYY
pat = re.compile(r'.*_(.*)(\d\d)')

def get_venue(citation_key):
    m = pat.match(citation_key)
    if m:
        return m.group(1) + "'" + m.group(2)
    else:
        raise ValueError("Non-conforming 'Citation key' field: " + citation_key)

def parse_extra_dict(s):
    a = s.split(': ')
    key = a[0]
    res = dict()
    for i in range(1, len(a)-1):
        aa = a[i].split(' ', 1)
        [val, newKey] = aa
        res[key] = val
        key = newKey
    res[key] = a[-1]
    return res

# turns dates like "2024-08-13" or "2024-08" into "August 2024"
def convert_date(d):
    try:
        date_obj = datetime.strptime(d, "%Y-%m-%d")
    except ValueError:
        date_obj = datetime.strptime(d, "%Y-%m")
    return date_obj.strftime("%B %Y")

def markdown_link(title, href):
    return f'[{title}]({href})'

def csv2md(csvPath, mdPath, title):
    papers = []

    with open(csvPath, newline='') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            papers.append(row)

    papers.sort(key=lambda row: row["Date"], reverse=True)

    with open(mdPath, 'w') as out:
        out.write('---\n')
        out.write('layout: default\n')
        out.write(f'title: "{title}"\n')
        out.write('---\n\n')
        out.write('## ' + title + '\n\n')
        for row in papers:
            extra_dict = parse_extra_dict(row["Extra"])
            out.write("|")
            out.write(get_venue(extra_dict["Citation Key"]))
            out.write("|")
            out.write(row["Author"])
            out.write(". **")
            out.write(row["Title"])
            out.write("**. *")
            out.write(row["Publication Title"])
            if row["Issue"]:
                out.write(" (")
                out.write(row["Issue"])
                out.write(")")
            out.write("*, ")
            out.write(convert_date(row["Date"]))
            out.write(". <br> [")
            # [ DOI | PDF | code ]
            out.write(markdown_link("DOI", "https://doi.org/" + row["DOI"]))
            out.write(" &#124; ") # |
            out.write(markdown_link("PDF", row["Url"]))
            out.write(" &#124; ") # |
            out.write(markdown_link("code", extra_dict["tex.code"]))
            out.write(f'] |\n')
        out.write('{: .kv }\n') # CSS class

csv2md("./publications.csv", "../publications.md", "Samuel Gruetter: Publications")
