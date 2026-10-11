## Worker report

The module `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover` states
`AlgebraicGeometry.universallyClosed_of_fpqc_cover`, the descent direction of Stacks
Tag 02KS. Its only proof is `sorry`; no definitions or additional nodes are needed.

Hypothesis and conclusion correspondence:
- Schemes X and S: `{X S : Scheme.{u}}`; the morphism: `(f : X ⟶ S)`.
- Arbitrary indexing set: `{I : Type v}`, with independently and explicitly declared
  universes u and v; no finiteness or nonemptiness assumption.
- The schemes S_i and maps g_i: `(S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)`.
- The family is an fpqc covering: `hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`.
  This is the dependency's recorded definition, not mere membership in the generated
  topology. It includes flatness and the finite affine-open image-cover condition.
  `fpqcPrecoverage` is `propQCPrecoverage @Flat`, the intersection of the quasi-compact
  precoverage and the jointly-surjective flat precoverage. The `QuasiCompactCover`
  condition uses compact opens; its `exists_isAffineOpen_of_isCompact` gives exactly
  the finite affine-open formulation in the node.
- The fibre product X ×_S S_i is `pullback f (g i)`, and f_i is its second projection
  `pullback.snd f (g i)`, with target S_i, not the projection to X.
- Every f_i is universally closed: `h : ∀ i, UniversallyClosed (pullback.snd f (g i))`.
  Mathlib's class quantifies over all base-change squares and requires the underlying
  topological maps to be closed. This includes the node's explanatory parenthesis
  about every T → S_i and the iterated fibre product.
- The conclusion is precisely `UniversallyClosed f`, with no separatedness,
  finite-type, quasi-compactness of individual g_i, or properness assumption.

Dependency declarations read and used:
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`; read both full structures and docstrings.
- `def-weil-pbc-fpqc-covering`: `AlgebraicGeometry.Scheme.fpqcPrecoverage`, from
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`; read its full definition and the underlying
  `propQCPrecoverage` and `QuasiCompactCover` definitions.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and `pullback.snd`, from
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; scheme pullbacks are
  provided by Mathlib. Read the full signatures and docstrings of both projections.
- `def-weil-proper-morphism`: `AlgebraicGeometry.UniversallyClosed`, listed in the
  dependency's `lean.declarations`, imported via its recorded module
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`. Read the class in
  `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed` and the `IsProper` signature.

Edge cases checked: the index set may be empty; an empty covering can satisfy hg
only for an empty target, in which case the conclusion is correct. Empty sources
and empty individual cover components are allowed. A singleton identity covering
makes h exactly the base-changed version of the conclusion. No characteristic,
Noetherian, affine, separated or nonempty restriction is imposed. u is arbitrary
for the schemes and v arbitrary for the family; there is no independently smaller
universe restricting the test schemes of universal closedness. The fpqc hypothesis
is substantive: an empty family over a nonempty scheme cannot satisfy it.

Source read: https://stacks.math.columbia.edu/tag/02KS, Lemma 35.23.3 and its full
proof (the local Stacks checkout is absent). The statement is unchanged and agrees
with its descent direction. The docstring records all five DAG proof steps:
isomorphism invariance, base-change stability, Zariski locality, affine flat
surjective descent, and application of the fpqc-local criterion 02KP.

Searches performed through `/home/ubuntu/weil-launcher/msearch.py`:
- LeanFinder, `Universally closed morphisms descend along an fpqc covering family`:
  eight hits; the nearest is
  `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`, which is
  descent along one morphism, not the required family statement. Other hits give
  Zariski locality, composition, and equivalent definitions.
- Loogle, `AlgebraicGeometry.UniversallyClosed, AlgebraicGeometry.Scheme.fpqcPrecoverage`:
  zero hits.
- LeanSearch, `universally closed fpqc covering descent`: unavailable, Internal
  Server Error. Recorded as unavailable, with no match verdict assigned.
- Mathlib grep, `universallyClosed|UniversallyClosed`, restricted to
  `AlgebraicGeometry/Sites`: zero hits.
- Direct rg over Mathlib, WeilConjectures and lean/Sheaf for the proposed name
  `universallyClosed_of_fpqc_cover`: zero hits.
- Direct rg over WeilConjectures and lean/Sheaf for
  `universallyClosed.*fpqc|UniversallyClosed.*fpqc|lem-weil-pbc-fpqc-descend-universally-closed`:
  only a reference to this DAG node in `IsProperOfFieldBaseChange.lean`; no statement.
- Direct rg for fpqc/Fpqc over the project's algebraic geometry directories:
  existing fpqc modules concern other properties, modules, or effective descent.
  In particular `FpqcClosedImmersionDescent.lean` states a different property;
  its family binder convention agrees with the present statement.
- Checked `dag/lean_names_upstream.json` for the item id with rg: no hit.

No node correction, dependency fault or statement dispute was found.

## Second reading by H1

I independently read the node, its four statement dependencies, the delivered
module, and the declarations below. No mathematical mismatch was found; the
Lean and node are unchanged. This reading adds only this report section.

Source check: the local Stacks .tex checkout is absent. I read the actual
`descent.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/descent.tex,
labels `definition-property-morphisms-local` (02KO) and
`lemma-descending-property-universally-closed` (02KS), together with the rendered
pages https://stacks.math.columbia.edu/tag/02KO and
https://stacks.math.columbia.edu/tag/02KS. Definition 02KO concerns schemes over
an arbitrary base and an arbitrary covering family. The reverse implication
in its equivalence is precisely this node; the ordering of the fibre-product
factors is immaterial, while the projection must target the covering component.
02KS assumes no finiteness, separatedness, characteristic or Noetherian condition.
Its affine hypotheses occur only in the reduction inside its proof. An ambient
base introduces no restriction for this absolute property (all schemes can be
regarded over Spec Z).

Object, hypothesis and conclusion checklist:

1. Schemes X and S, and their morphism f: `{X S : Scheme.{u}} (f : X ⟶ S)`.
   PASS. I read `Scheme` and `Scheme.Hom` in Mathlib's Scheme.lean: locally
   ringed spaces locally isomorphic to affine spectra, and morphisms of the
   underlying locally ringed spaces. These are the matches of def-pc-scheme.
2. Arbitrary index set I, schemes S_i and arrows g_i to S:
   `{I : Type v} (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)`.
   PASS. Neither finite nor nonempty indices nor affine components are required.
3. The family is an fpqc covering:
   `hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S`.
   PASS. I read the match of def-weil-pbc-fpqc-covering in Fpqc.lean,
   `propQCPrecoverage` in Sites/QuasiCompact.lean, and `QuasiCompactCover`
   in Cover/QuasiCompact.lean. They require flat arrows, joint surjectivity,
   and finite compact-open image covers of each affine open of S.
   `QuasiCompactCover.exists_isAffineOpen_of_isCompact` explicitly supplies
   finite affine-open image covers, exactly the dependency node's formulation.
   Conversely affine opens are compact. Joint surjectivity follows from that
   condition and introduces no stronger assumption. `Presieve.ofArrows` records
   precisely the supplied arrows (read its inductive declaration in Sieves.lean),
   so repetitions of the same arrow do not change the covering condition.
4. X ×_S S_i and its projection f_i to S_i:
   `pullback f (g i)` and `pullback.snd f (g i)`.
   PASS. I read pullback and both projection signatures in HasPullback.lean,
   the recorded Mathlib match of def-pc-fibre-product; snd targets the source
   of the second argument, S_i. Scheme pullbacks are available without an
   additional assumption on f or g_i.
5. Each f_i is universally closed, meaning closed after every further base
   change: `h : ∀ i, UniversallyClosed (pullback.snd f (g i))`.
   PASS. def-weil-proper-morphism records UniversallyClosed among its
   `lean.declarations`, exposed by its Proper module. I read the actual class
   in UniversallyClosed.lean: `universally (topologically @IsClosedMap) f`.
   This is the node's condition on every T → S_i, rather than closedness alone.
6. Conclusion f universally closed: `: UniversallyClosed f`.
   PASS. The same predicate is used in hypothesis and conclusion; no properness
   or finite-type conclusion has been substituted. All objects precede hg and h,
   and h precedes the conclusion, exactly as in the node.

Edge cases: I empty is allowed; joint surjectivity then forces S empty, and
any X → S forces X empty as well, so universal closedness is correct. Empty X,
empty individual S_i, and empty S are all allowed. For a singleton identity
cover the hypothesis is universal closedness of the canonically isomorphic
base change. The finite affine refinements may use n = 0, as is appropriate
for the empty open. There is no field or characteristic parameter, and no
zero-object assumption; empty spectra (including the zero ring) are covered.
Both universes u and v are explicitly bound and arbitrary: the index universe
is independent of the scheme universe. The standard UniversallyClosed class
supplies the test-scheme quantification; no separately smaller test universe
or extra instance restricts it. All schemes in any particular family can be
placed in one sufficiently large universe.

Independent searches (with alternative wording):

- LeanFinder via msearch.py, `Closedness under all base changes can be checked
  on a faithfully flat covering family`: eight hits, concerning flatness and
  faithfully-flat ring descent; no family statement for universal closedness.
- Loogle via msearch.py,
  `AlgebraicGeometry.UniversallyClosed, CategoryTheory.Presieve.ofArrows`:
  zero hits.
- LeanSearch via msearch.py,
  `universal closedness descent covering family flat schemes`: service
  unavailable (Internal Server Error); no match verdict assigned.
- Direct rg for `UniversallyClosed|universallyClosed|IsClosedMap|02KS` in
  Mathlib's algebraic-geometry Sites and FlatDescent, and for
  `UniversallyClosed|universallyClosed|02KS` throughout WeilConjectures and
  lean/Sheaf: no existing family-descent statement. The proposed declaration
  and source label also have no hit in dag/lean_names_upstream.json.
  I opened Mathlib's
  `descendsAlong_universallyClosed_surjective_inf_flat_inf_quasicompact`:
  its signature is `DescendsAlong @UniversallyClosed
  (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`, concerning one morphism, not this
  fpqc family. Thus it does not justify dropping the delivered module.

H5/H6/H8/H9: no definitions (hollow or duplicated), no new nodes or dependency
modules, and only one named theorem with proof `by sorry`. The module and
statement docstrings identify 02KS and this blueprint id. The five numbered
proof steps faithfully carry the node's iso invariance, base-change stability,
Zariski locality, affine descent and final 02KP application, naming every
supporting node. Imports expose the recorded fpqc and universal-closedness
notions. Namespace, header and line lengths follow the conventions. No
statement_change exists or is needed, so corrected-statement citer checks are
inapplicable. The node's lean.statement is verbatim the theorem signature.

Validation: scompile.py on the absolute sandbox module path compiled on the
server in 1.7 seconds, exit code 0, with no errors or warnings. The initial
relative-path invocation was made from the read-only repository and could not
find the sandbox file; rerunning with its absolute path resolved that invocation
error. By inspection, every variable and universe is explicitly bound.
