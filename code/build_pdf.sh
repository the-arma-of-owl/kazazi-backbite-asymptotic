#!/bin/bash
# paper/asymptotic_threshold.md -> paper/asymptotic_threshold.pdf  (pandoc + tectonic)
set -e
cd "$(dirname "$0")/../paper"
cat > /tmp/_hdr.tex <<'H'
\usepackage{amsmath,amssymb}
\usepackage[margin=2.5cm]{geometry}
\usepackage{microtype}
\usepackage{xurl}
H
pandoc asymptotic_threshold.md -o asymptotic_threshold.tex --standalone -H /tmp/_hdr.tex -V fontsize=11pt -V colorlinks=true
tectonic -X compile asymptotic_threshold.tex
rm -f asymptotic_threshold.tex
