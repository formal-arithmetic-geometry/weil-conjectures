## Worker report

The module `Sheaf.AlgebraicGeometry.FpqcAffineDescent` states
`AlgebraicGeometry.isAffineHom_of_fpqc_cover`, with its sole proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Clause-by-clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`; the scheme morphism f: `(f : X ⟶ S)`.
- An arbitrary indexing set I: `{I : Type v}`, with its universe independent of u.
- The family of schemes and maps to S: `(S' : I → Scheme.{u})` and
  `(g : ∀ i, S' i ⟶ S)`.
- The family is fpqc: `(hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)`.
  This uses the exact declaration recorded on def-weil-pbc-fpqc-covering. Membership
  requires flatness, joint surjectivity, and quasi-compactness of the family, not
  quasi-compactness of each component map. Mathlib's `QuasiCompactCover` condition
  on compact opens is equivalent to the node's finite affine-open image condition:
  use the affine-open basis to refine compact opens finitely, as in
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact`.
- The base change f_i is the second projection of the chosen fibre product:
  `pullback.snd f (g i)` has source `pullback f (g i)` and target `S' i`.
- Every f_i is affine: `(h : ∀ i, IsAffineHom (pullback.snd f (g i)))`.
- The conclusion that f is affine: `IsAffineHom f`.

Dependency declarations read and used:

- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (local affine charts on a locally ringed space;
  morphisms of underlying locally ringed spaces).
- def-weil-pbc-fpqc-covering: `AlgebraicGeometry.Scheme.fpqcPrecoverage`,
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`; also read the defining
  `QuasiCompactCover` in `Mathlib.AlgebraicGeometry.Cover.QuasiCompact`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback` and `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, with the scheme
  pullback instance supplied transitively by the fpqc import.
- pqf-def-affine-morphism: `AlgebraicGeometry.IsAffineHom`,
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`; its field is exactly affineness
  of inverse images of affine opens. All dependencies are Mathlib leaves and
  have no `lean` record to repair.

Edge cases checked before writing: I may be empty, in which case fpqc membership
forces the base empty; no nonempty assumption was added. Empty source and empty
base are allowed. Neither schemes nor component maps are required to be affine,
quasi-compact, separated, or of finite type. The indexing universe v is unrestricted;
there are no quantified test schemes in a smaller universe. No field or
characteristic restrictions occur. The morphism f is arbitrary, so the covering
and affineness hypotheses are substantive conditions, not automatic instances.

Searches:

- `msearch.py ... leanfinder "Affine morphisms of schemes descend along fpqc covering families"`:
  eight hits, principally `HasAffineProperty.descendsAlong_of_affineAnd`,
  `HasAffineProperty.of_openCover` and affine-cover constructions; no exact family theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffineHom, CategoryTheory.MorphismProperty.DescendsAlong"`:
  one hit, `HasAffineProperty.descendsAlong_of_affineAnd`, which assumes affine descent.
- `msearch.py ... grep "DescendsAlong.*IsAffineHom|affine.*fpqc|IsAffineHom.*fpqc" AlgebraicGeometry`:
  only Mathlib `Morphisms/Descent.lean:194`, a hypothesis of that generic theorem.
- `msearch.py ... leansearch "If all base changes of a scheme morphism along an fpqc covering family are affine then the morphism is affine"`:
  unavailable (HTTP Internal Server Error); no negative verdict is inferred.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id,
  affine/fpqc combinations and `DescendsAlong.*IsAffineHom` found the source
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent` theorem
  `IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact`.
  Its full signature/docstring were read: it handles one flat surjective
  quasi-compact morphism, not the node's arbitrary family. The generic family
  theorem `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` was also read; it is
  parametrized by a property P and requires its descent as an additional instance,
  and thus is not this node's statement either.
- `rg` of these patterns in the project's `lean/Sheaf` found only citations of
  this node (notably FpqcClosedImmersionDescent) and unrelated fpqc refinements.
  The proposed full declaration name was searched in Mathlib, the source,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

The local Stacks TeX file is absent on this machine. Read the original source
at https://stacks.math.columbia.edu/tag/02L5 instead. It agrees with the node;
no disputed statement or node fault was found. The docstring carries all eight
steps of the DAG proof with their dependency ids. All variables and universes
are bound explicitly. Verification: server single-file compile and the delivery
dry run (results recorded by the tools).

## Second reading by K1

I independently read the node, all four statement-dependency nodes, the module,
and the defining Mathlib signatures. No mathematical or Lean mismatch was found;
no module or node field was changed. This section is the only manual change.

Source check: the local Stacks checkout is absent. I fetched the original
`descent.tex` into this item's scratchpad and read lines 5925–5965, together with
`definition-property-morphisms-local` (02KO). I also read the official pages
[02L5](https://stacks.math.columbia.edu/tag/02L5),
[02KO](https://stacks.math.columbia.edu/tag/02KO), and
[022B](https://stacks.math.columbia.edu/tag/022B). The node selects precisely the
cover-to-base direction of fpqc locality for affineness. There is no ambient
Noetherian, field, separatedness, or finite-type hypothesis; affine bases in the
source proof are a reduction, not hypotheses of the lemma.

Objects, hypotheses and conclusion, item by item (H3):

- Schemes X and S: `{X S : Scheme.{u}}`. PASS. `Scheme` is Mathlib's locally
  ringed space with local affine charts (Scheme.lean:42); `Scheme.Hom` (line 74)
  is the locally ringed-space morphism. These are def-pc-scheme's objects.
- Arbitrary morphism f from X to S: `(f : X ⟶ S)`. PASS. No extra instance on f.
- Arbitrary index set I: `{I : Type v}` with explicitly bound, independent v.
  PASS. No finiteness or nonemptiness restriction.
- Schemes S_i and morphisms g_i to S: `(S' : I → Scheme.{u})`
  and `(g : ∀ i, S' i ⟶ S)`. PASS. Same family and quantifier order.
- The family is fpqc: `(hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)`.
  PASS. I read fpqcPrecoverage (Fpqc.lean:60), propQCPrecoverage
  (Sites/QuasiCompact.lean:112), Scheme.precoverage, and QuasiCompactCover
  (Cover/QuasiCompact.lean:38). These require flat arrows, joint surjectivity,
  and the finite compact-open image condition on every affine target open.
  The latter is precisely the recorded def-weil-pbc-fpqc-covering notion:
  refine each compact open by finitely many affine opens, allowing repeated
  family indices. The explicit theorem
  `QuasiCompactCover.exists_isAffineOpen_of_isCompact` (line 62) gives the
  affine-open form, and affine opens are compact for the converse.
  Joint surjectivity follows from the node's affine-open condition. There is
  no extra assumption that each g_i itself is quasi-compact.
- The fibre product and its second projection f_i: `pullback.snd f (g i)`.
  PASS. I read `pullback` and `pullback.snd` in HasPullback.lean:95,115:
  the domain is `pullback f (g i)` and the target is `S' i`, exactly
  def-pc-fibre-product's chosen base change. Scheme pullbacks are supplied
  by the Mathlib import; no HasPullback hypothesis is added to the statement.
- Every f_i affine: `(h : ∀ i, IsAffineHom (pullback.snd f (g i)))`.
  PASS. I read IsAffineHom in Morphisms/Affine.lean:47–48. It requires precisely
  affine preimages of affine opens, as pqf-def-affine-morphism states.
- Conclusion f affine: `IsAffineHom f`. PASS, with no omitted or added clause.

Edge cases: I may be empty; joint surjectivity then forces S empty and existence
of f forces X empty. Empty sources or empty component schemes are allowed.
An empty scheme is affine (the zero-ring spectrum), and the fpqc condition
allows zero affine opens in its finite covering witness. No nonzero-ring or
field restriction is introduced, hence all characteristics are covered.
There is no numerical parameter n in the theorem; n = 0 remains allowed in
its covering definition. Arbitrary u and independent index universe v are
bound. All schemes live in Mathlib's single scheme category at u, which can
be chosen large enough for any given family; there is no quantified test object
in a smaller universe. Covering and affineness are substantive hypotheses,
not tautological identity-map conditions.

Independent H4 searches, using different wording from the first worker:

- LeanFinder via msearch: "affineness of a morphism can be checked on a
  faithfully flat covering of its target". Eight hits, chiefly
  `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine` and flatness
  characterizations; none states this covering-family theorem.
- Loogle via msearch: `AlgebraicGeometry.IsAffineHom,
  CategoryTheory.Limits.pullback.snd`. Zero hits.
- rg of Mathlib/AlgebraicGeometry, WeilConjectures, and repository lean/Sheaf
  for `affine.*descen|descen.*affine|IsAffineHom.*of.*(cover|flat)|02L5`.
  I opened `IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact`
  in the source FlatDescent module: it is a single flat surjective
  quasi-compact base-change theorem. I also opened the generic
  `Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology`, including its ambient
  P hypotheses. It assumes descent of P and stability/locality of P, so it
  does not itself state this node. Mathlib's generic
  `HasAffineProperty.descendsAlong_of_affineAnd` assumes affine descent.
  `CategoryTheory.Over.DescentDatum.isEffective_of_isAffineHom_fpqc` in the
  project's AffineFpqcDescent module is effectivity of descent data, a
  different statement. Other hits concern limits, modules or specialized
  covers. No exact duplicate was found.
- The proposed full name is absent in these trees and
  `dag/lean_names_upstream.json`. The worker's failed LeanSearch is already
  recorded above; no negative conclusion is inferred from that failure.

H5/H6/H8/H9: the delivery has no definitions, no private copied notion, no new
nodes, and no dependency modules. All four dependencies are usable Mathlib
leaves. There is exactly one named theorem and its only proof is `sorry`.
The module and theorem docstrings cite Stacks 02L5 and the blueprint id.
The theorem docstring follows each of the eight DAG proof steps, including
qcqs descent, flat base change, canonical-map comparison by cartesian pasting,
and isomorphism descent. Namespace, header, topic path and 100-character width
are correct. The fpqc import provides the notions used. Every variable and
universe is explicitly bound. The node has no statement correction, so citer
revalidation for a correction is inapplicable. The node's lean.statement was
checked verbatim against the file's signature, including binder order.

Validation: reran the authorized server single-file compile and delivery dry
run; results are recorded by the tools. Second reading changed no Lean or
mathematical content; it added this independent correspondence and source audit.
