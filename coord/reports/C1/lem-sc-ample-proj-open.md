## Worker report

The module `Sheaf.AlgebraicGeometry.AmpleProjOpen` states
`AlgebraicGeometry.exists_isOpenImmersion_proj_of_isAmple`, with proof `sorry`.
It defines no new notions. The node is unchanged outside its `lean` record.

Hypothesis and clause correspondence:
- “Let X be a scheme”: `(X : Scheme.{u})`.
- “an invertible sheaf L”: `(L : X.Modules) [L.IsInvertible]`, using the recorded
  local rank-one definition, not the stronger relative/projective ampleness notion
  elsewhere in the source repository.
- “ample”: `(hL : Scheme.Modules.IsAmple X L)`. This recorded absolute notion
  already includes quasi-compactness and positive tensor-power sections with affine
  nonvanishing neighbourhoods, so no separate hypothesis is added.
- “there exist a ... commutative ring S”: `∃ (S : Type u) (_ : CommRing S)`.
- “nonnegatively graded”: `(𝒮 : ℕ → AddSubgroup S) (_ : GradedRing 𝒮)`.
  GradedRing requires a direct-sum decomposition, a degree-zero unit and the
  multiplication law. AddSubgroup components are the general internally graded
  commutative-ring model, not an algebra over a chosen field or a standard grading.
- “an open immersion X → Proj(S)”: `(f : X ⟶ Proj 𝒮), IsOpenImmersion f`.
  No prescribed section ring, equality of pullback line bundles, finite generation,
  standard grading or additional conclusion is required by the node.

Dependencies read and used:
- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (via the dependency imports).
- `def-sc-invertible-module`: WeilConjectures.AlgebraicGeometry.Modules.Invertible,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (via Ample).
- `def-weil-pbc-ample-invertible-module`: Sheaf.AlgebraicGeometry.Ample,
  `AlgebraicGeometry.Scheme.Modules.IsAmple`, imported directly.
- `def-pc-proj`: Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme,
  `AlgebraicGeometry.Proj`, imported directly. The accompanying recorded
  `AlgebraicGeometry.projIsoSpec` and `ProjectiveSpectrum.basicOpen` signatures
  and docstrings were read; the existential statement does not itself mention charts.
- Mathlib.AlgebraicGeometry.OpenImmersion, `AlgebraicGeometry.IsOpenImmersion`
  gives the actual scheme open-immersion predicate, imported directly.

The proof docstring reproduces all three node steps and names both proof dependencies:
the finite affine cover, the canonical chart morphism and its local isomorphisms,
then gluing to the open image. No step is proved at this stage.

Edge cases checked before writing:
- The empty scheme is admitted: no Nonempty binder, and a zero ring or empty Proj
  is permitted. The section-ring construction still makes sense.
- Affine X with the structure sheaf fits (one can take a polynomial ring in one
  degree-one variable); no finite-type assumption on its ring is imposed.
- Projective space with O(1) fits; a negative line bundle is not assumed ample.
- Degree zero and positive degrees are distinguished by the recorded ampleness
  predicate; the conclusion admits arbitrary N-gradings, including gaps.
- No field, characteristic, Noetherian, reducedness or separatedness hypothesis
  is inserted. All universes and variables are explicit. `u` is arbitrary;
  the section ring of a Scheme.{u} and its sheaf of modules can be formed in
  Type u, so its witness universe does not exclude any scheme in the input universe.

Searches for an existing statement (2026-10-11):
- msearch leanfinder: “A scheme with an ample invertible sheaf admits an open
  immersion into Proj of a nonnegatively graded commutative ring”: eight hits,
  generic Proj constructions and chart open immersions; none proves this theorem.
- msearch loogle: “AlgebraicGeometry.Proj, AlgebraicGeometry.IsOpenImmersion”:
  four hits, away-chart immersions and affine-cover formulas only.
- msearch grep: “ample.*Proj|Proj.*ample|IsAmple”, Mathlib/AlgebraicGeometry:
  zero hits.
- msearch leansearch: “scheme ample invertible sheaf open immersion Proj graded
  ring”: service unavailable (Internal Server Error); no verdict inferred.
- rg over WeilConjectures and lean/Sheaf: “ample.*proj|proj.*ample|lem-sc-ample-proj-open”
  case insensitive: the source's ProjectiveSpace.OfAmple concerns immersions into
  finite projective space with affine base, separatedness and local finite type;
  its full theorem signature was inspected and does not state this node.
  Other hits concern projectivity, cohomology or unrelated “example” text.
- rg over dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for
  “exists.*[Pp]roj|openImmersion.*ample|exists_openImmersion_proj_of_isAmple”:
  no declaration matching this statement; related projective-space theorems only.
  The chosen full declaration name has no existing occurrence.

Source check: the local Stacks TeX file is absent on this machine. Read the
primary online source https://stacks.math.columbia.edu/tag/01Q3 (condition 1 to 2)
and https://stacks.math.columbia.edu/tag/01Q1. The stronger source result supplies
exactly the existential consequence the node states. Quasi-compactness is already
part of the recorded absolute ampleness definition. No statement correction or
STATEMENT-DISPUTED issue was needed.

## Second reading by C1

I independently compared the node with `AmpleProjOpen.lean` and found the statement faithful.
The correspondence is item by item:

- The scheme `X` is `(X : Scheme.{u})`, using Mathlib's `AlgebraicGeometry.Scheme`.
- The invertible sheaf is `(L : X.Modules)` with the instance `[L.IsInvertible]`, exactly
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` from the dependency node.
- Absolute ampleness is `(hL : Scheme.Modules.IsAmple X L)`, the project's
  `def-weil-pbc-ample-invertible-module` (quasi-compactness plus affine nonvanishing loci
  of positive tensor powers). This is not the relative `AlgebraicGeometry.IsAmple` in the
  source repository, and the imported `Sheaf.AlgebraicGeometry.Ample` declaration is the
  recorded absolute notion.
- The existential ring is `∃ (S : Type u) (_ : CommRing S)`, and its grading is
  `(𝒮 : ℕ → AddSubgroup S) (_ : GradedRing 𝒮)`, matching a nonnegative graded
  commutative ring. The target is `(f : X ⟶ Proj 𝒮), IsOpenImmersion f`, with
  Mathlib's `AlgebraicGeometry.Proj` and `AlgebraicGeometry.IsOpenImmersion`.
  The quantifier order is unchanged and no section-ring equality, finite generation,
  standard grading, or other conclusion was added.

The universe `Type u` is sufficient for the section ring construction and does not exclude
any input `Scheme.{u}`. No Noetherian, separated, reduced, characteristic, field, or
finite-type hypothesis is present. Empty schemes, zero-degree components, grading gaps,
and the empty/zero ring edge cases are admitted by the signature; ampleness supplies the
cover required by the source argument. The affine structure-sheaf and projective-space
examples were checked as sanity cases, while a negative line bundle is excluded by `hL`.

I repeated the existing-definition searches with `msearch.py` (LeanFinder, Loogle and
LeanSearch queries for an ample invertible sheaf and an open immersion into Proj), `rg`
over Mathlib, `WeilConjectures`, and `lean/Sheaf`, and direct inspection of the dependency
modules. No declaration states this theorem. The source is Properties Proposition 01Q3
(1) => (2), via Lemma 01Q1; the module docstring and theorem docstring carry that source
and the three proof steps from the node.

No mathematical mismatch was found. The only delivery change was recording the exact Lean
signature in the node's `lean` field; the worker module and theorem body remain unchanged.
The module compiles cleanly with `scompile.py`.
