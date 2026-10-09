#!/usr/bin/env bash
# Rebuild literature/ on a fresh machine from the sources recorded in literature/LIST.md ("Obtained" table).
# Usage: tools/fetch_literature.sh [--dry]      run from the project root; needs curl and git; idempotent (skips files that exist).
# What it fetches: every PDF of the Obtained table by its URL; the Stacks project and the two blueprint branches by git clone at
# the recorded commits. What it cannot fetch is listed at the end of LIST.md ("Rebuilding literature/").
set -u
cd "$(dirname "$0")/.."
DRY=${1:-}
get() { # get <url> <target>
  local url=$1 out=$2
  if [ -s "$out" ]; then echo "have   $out"; return; fi
  echo "fetch  $out  <-  $url"
  [ "$DRY" = "--dry" ] && return
  mkdir -p "$(dirname "$out")"
  curl -fsSL -A "Mozilla/5.0 (sheaf-dag literature fetch)" -o "$out" "$url" || { echo "FAILED $url" >&2; rm -f "$out"; }
}
clone() { # clone <repo> <branch> <commit> <dir>
  local repo=$1 branch=$2 commit=$3 dir=$4
  if [ -d "$dir/.git" ]; then echo "have   $dir"; return; fi
  echo "clone  $dir  <-  $repo @ $branch $commit"
  [ "$DRY" = "--dry" ] && return
  git clone --quiet --branch "$branch" "$repo" "$dir" && git -C "$dir" checkout --quiet "$commit"
}
L=literature
# PDFs (URL and file name as in LIST.md)
get http://www.numdam.org/item/PMIHES_1974__43__273_0.pdf   $L/deligne-weil-I_PMIHES-1974-43.pdf
get http://www.numdam.org/item/PMIHES_1980__52__137_0.pdf   $L/deligne-weil-II_PMIHES-1980-52.pdf
get http://www.numdam.org/item/PMIHES_1987__65__131_0.pdf   $L/laumon-transformation-de-fourier_PMIHES-1987-65.pdf
get https://www.numdam.org/item/AST_1982__100__1_0.pdf      $L/bbd-faisceaux-pervers_Asterisque-100-1982.pdf
get https://math.stanford.edu/~conrad/papers/nagatafinal.pdf $L/conrad-deligne-notes-on-nagata-compactifications.pdf
get https://math.stanford.edu/~conrad/Weil2seminar/Notes/etnotes.pdf $L/conrad-etale-cohomology-notes.pdf
for n in 18 19 20 22 23 24; do get https://math.stanford.edu/~conrad/Weil2seminar/Notes/L$n.pdf $L/stanford-weil2-seminar/L$n.pdf; done
get https://www.jmilne.org/math/CourseNotes/LEC.pdf         $L/milne-lectures-on-etale-cohomology_LEC.pdf
get https://www.jmilne.org/math/CourseNotes/AV.pdf          $L/milne-abelian-varieties_AV.pdf
get https://www.jmilne.org/math/Books/iAG2017.pdf           $L/milne-algebraic-groups_iAG2017.pdf
get https://arxiv.org/pdf/1309.1198                         $L/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf
get https://arxiv.org/pdf/math/0505564                      $L/varshavsky-lefschetz-verdier-trace-formula_arXiv-math0505564.pdf
get https://arxiv.org/pdf/2305.18131                        $L/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf
get https://arxiv.org/pdf/2601.07358                        $L/ruimy-tubach-wolf-proetale-motives-solid-rigidity_arXiv-2601.07358.pdf
get https://arxiv.org/pdf/2510.07443                        $L/haine-et-al-condensed-homotopy-type_arXiv-2510.07443.pdf
get https://arxiv.org/pdf/1006.3810                         $L/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf
get https://arxiv.org/pdf/2412.19605                        $L/bergfalk-lambie-hanson_arXiv-2412.19605.pdf
get https://arxiv.org/pdf/0901.3322                         $L/juteau-mautner-williamson-perverse-sheaves-modular-rep_arXiv-0901.3322.pdf
get https://arxiv.org/pdf/1207.3648                         $L/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf
get https://people.mpim-bonn.mpg.de/scholze/SixFunctors.pdf  $L/scholze-six-functor-formalisms.pdf
get https://math.mit.edu/~poonen/papers/bertini_irred.pdf    $L/charles-poonen-bertini-irreducibility.pdf
get http://www.numdam.org/item/ASENS_1968_4_1_1_149_0.pdf    $L/tate-residues-of-differentials-on-curves_ASENS-1968.pdf
get http://www.numdam.org/item/CM_1988__65_2_121_0.pdf       $L/spaltenstein-resolutions-of-unbounded-complexes_CM-1988.pdf
get https://www.math.ucla.edu/~balmer/Pubfile/IdempCompl.pdf $L/balmer-schlichting-idempotent-completion.pdf
get https://www.numdam.org/item/SB_1964-1966__9__287_0.pdf   $L/grothendieck-groupe-de-brauer-II_SemBourbaki-297.pdf
get https://arxiv.org/pdf/math/0206203                       $L/sga/SGA1_arXiv-math0206203.pdf
for n in 05 06 07 08 09 10 11 12 13 14 15 16 17 18; do get http://www.normalesup.org/~forgogozo/SGA4/$n/$n.pdf $L/sga/SGA4-expose-${n}_reedition.pdf; done
get https://www.numdam.org/item/PMIHES_1961__8__5_0.pdf      $L/ega/EGA-II_PMIHES-8-1961.pdf
get https://www.numdam.org/item/PMIHES_1961__11__5_0.pdf     $L/ega/EGA-III-1_PMIHES-11-1961.pdf
get https://www.numdam.org/item/PMIHES_1964__20__5_0.pdf     $L/ega/EGA-IV-1_PMIHES-20-1964.pdf
get https://www.numdam.org/item/PMIHES_1965__24__5_0.pdf     $L/ega/EGA-IV-2_PMIHES-24-1965.pdf
get https://www.numdam.org/item/PMIHES_1966__28__5_0.pdf     $L/ega/EGA-IV-3_PMIHES-28-1966.pdf
# git sources at the recorded commits
clone https://github.com/stacks/stacks-project master a04446e57ec1fbc252a871afcec7752fb2807b14 $L/stacks-project
clone https://github.com/formal-arithmetic-geometry/weil-conjectures master      967897d1c5e775be739997d7e847a9205fae1359 $L/blueprint/master
clone https://github.com/formal-arithmetic-geometry/weil-conjectures slopmaster2 1ad77be92cebdbd62febaca30a77fa594d1a23a5 $L/blueprint/slopmaster2
[ "$DRY" = "--dry" ] || printf 'master 967897d1c5e775be739997d7e847a9205fae1359  slopmaster2 1ad77be92cebdbd62febaca30a77fa594d1a23a5\n' > $L/blueprint/COMMITS.txt
echo "done; see literature/LIST.md 'Rebuilding literature/' for what this script cannot fetch"
