## Worker report

The module `Sheaf.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite` states
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_of_isLocallyQuasiFinite` with a
single `sorry` proof. It introduces no definitions and changes only the item's
`lean` record. There are no new nodes, dependency modules, or statement corrections.

Hypotheses and conclusion, clause by clause:

- Schemes X and S: `{X S : Scheme.{u}}`; the arbitrary explicit universe u is the
  same universe used by the recorded quasi-finite-morphism definition.
- A morphism f : X → S: `(f : X ⟶ S)`.
- Locally quasi-finite: `(hf : f.IsLocallyQuasiFinite)`, using exactly the recorded
  `pqf-def-quasifinite` definition. Unfolding this predicate gives
  `∀ x : X, IsQuasiFiniteAtPoint f x`.
- For every x, an affine open neighbourhood U containing x: that recorded
  pointwise predicate binds `(U : X.Opens) (hx : x ∈ U) (hU : IsAffineOpen U)`.
- An affine open V in S: `(V : S.Opens) (_ : IsAffineOpen V)` in the same definition.
- The image of U lies in V: its witness `(e : U ≤ f ⁻¹ᵁ V)`.
- The induced map on sections R = O_S(V) → A = O_X(U): the same definition uses
  `(f.appLE V U e).hom.toAlgebra`, so the algebra is the specified map, not an
  arbitrary algebra structure.
- Finite type of that ring map: `∃ hft : Algebra.FiniteType Γ(S, V) Γ(X, U)`
  under that induced algebra structure, then `letI := hft`.
- Quasi-finiteness at the prime corresponding to x:
  `Algebra.IsQuasiFiniteAtPrime Γ(S, V) Γ(X, U) (hU.primeIdealOf ⟨x, hx⟩)`.
  The recorded ring predicate means the corresponding fibre prime is isolated,
  expressed by `IsOpen` of its singleton in `PrimeSpectrum (p.asIdeal.Fiber S)`.
- Conclusion: `LocallyOfFiniteType f`, exactly the recorded predicate for
  `def-weil-finite-type-morphism`. Its all-affine-pairs characterization agrees
  with the node's affine-cover characterization by Stacks Tag 01T2.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint`, including their full
  definitions and docstrings. This is the single direct import.
- `Sheaf.RingTheory.QuasiFiniteAtPrime`: `Algebra.IsQuasiFiniteAtPrime`, used
  through the preceding recorded definition (full definition/docstring read).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, and `Spec.map`.
  Affine spectra are represented by `IsAffineOpen` inside the dependency.
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.homEquiv`, read to
  check the spectrum dependency's contravariant ring-map convention.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`, used inside the hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, used as the conclusion.

The proof docstring follows both DAG steps: drop the quasi-finiteness clause to
obtain a finite-type affine pair around each point; then apply
`lem-weil-pbc-lft-pointwise-criterion`. The relevant Mathlib declaration
`HasRingHomProperty.iff_exists_appLE` was also read in RingHomProperties.lean;
it is a stage-3 proof input, not a hypothesis or a new theorem here.

Source check: the local `literature/stacks-project/morphisms.tex` is absent on
this machine. Read the primary source online instead:
[01TD](https://stacks.math.columbia.edu/tag/01TD), the remark immediately following
it in [01TC](https://stacks.math.columbia.edu/tag/01TC), and
[01T2](https://stacks.math.columbia.edu/tag/01T2). They agree with the unchanged node.

Edge cases checked before writing: the empty source makes the pointwise hypothesis
vacuous and the conclusion valid; an empty target admits only an empty source.
No quasi-compactness, Noetherian, separatedness, base field, characteristic,
nonemptiness, or global finite-type assumption is introduced. A non-quasi-compact
disjoint union of points over a field remains permitted, so the conclusion is
local finite type only. An arbitrary field extension need not be locally quasi-finite
in this Stacks sense; finite type has not been discarded from the hypothesis.
All variables and universes in the new signature are explicitly bound.

Searches performed (msearch commands were for group M1 and this item):

- LeanFinder: `locally quasi-finite morphism of schemes is locally of finite type`:
  eight hits including Mathlib LocallyQuasiFinite, LocallyOfFiniteType, and finite
  morphism instances; no exact statement using the Stacks predicate.
- Loogle: `AlgebraicGeometry.LocallyQuasiFinite, AlgebraicGeometry.LocallyOfFiniteType`:
  nine hits, all using local finite type as an assumption rather than deriving it.
- LeanSearch: `locally quasi finite scheme morphism implies locally of finite type`:
  service unavailable (Internal Server Error); recorded as unavailable.
- msearch grep: `LocallyQuasiFinite|IsLocallyQuasiFinite` in
  `AlgebraicGeometry/Morphisms`: five hits in Mathlib QuasiFinite.lean. Read its
  class and docstring: local finite type is explicitly not required.
- Direct rg on source `WeilConjectures` and project `lean/Sheaf`:
  `locallyOfFiniteType.*[Qq]uasi|[Ll]ocally[Qq]uasi[Ff]inite.*[Ff]inite[Tt]ype|lem-weil-pbc-lqf-locally-finite-type`:
  source results use local finite type as a separate assumption or concern
  different morphisms; no exact statement. The project contains the usable
  recorded definition, which is imported without copying it.
- Direct rg `IsLocallyQuasiFinite|locallyOfFiniteType_of_isLocallyQuasiFinite`
  on project Lean and `dag/lean_names_upstream.json`: only the recorded predicate.
- Direct rg for the chosen theorem name on Mathlib, source `WeilConjectures`,
  project Lean, and `dag/lean_names_upstream.json`: no hits, so no name collision.

Validation: server single-file compile completed successfully in 1.6 seconds,
exit code 0, no warnings. Delivery dry-run result is recorded below after running it.


## Second reading by M1

Read the item node, its delivered signature, every statement-dependency node and
its recorded declaration, and the bodies of `IsQuasiFiniteAtPoint`,
`IsLocallyQuasiFinite`, and `Algebra.IsQuasiFiniteAtPrime`. The local Stacks checkout
is absent; independently read the primary Stacks pages
https://stacks.math.columbia.edu/tag/01TC and
https://stacks.math.columbia.edu/tag/01T2, and the actual `morphisms.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/morphisms.tex,
at `definition-quasi-finite`, its following remark, and `definition-finite-type`.
These introduce arbitrary schemes and a morphism; no section-wide Noetherian,
separatedness, quasi-compactness, field, or characteristic hypothesis applies.

Node statement checklist, with its Lean rendering and verdict:

1. Objects X and S are schemes: `{X S : Scheme.{u}}`. Mathlib `Scheme` is a
   locally ringed space locally isomorphic to spectra, as def-pc-scheme requires.
   Verdict: exact.
2. The specified morphism f from X to S: `(f : X ⟶ S)`. Its direction agrees with
   the node and Mathlib's scheme category. Verdict: exact.
3. Local quasi-finiteness: `(hf : f.IsLocallyQuasiFinite)`, the recorded
   pqf-def-quasifinite declaration, whose body is
   `∀ x : X, IsQuasiFiniteAtPoint f x`. The order is every x followed by local
   witnesses depending on x, rather than one common affine pair. Verdict: exact.
4. An affine open neighbourhood U of each x: the body binds
   `(U : X.Opens) (hx : x ∈ U) (hU : IsAffineOpen U)`.
   Mathlib's affine-open identification supplies Spec of its section ring and
   `hU.primeIdealOf ⟨x, hx⟩ : PrimeSpectrum Γ(X, U)` is the corresponding point
   under `hU.isoSpec.hom`, not an arbitrary prime. Verdict: exact.
5. An affine target open V with f(U) contained in V: the same body binds
   `(V : S.Opens) (_ : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)`.
   The inclusion is exactly image containment. Verdict: exact.
6. The specified section-ring map R to A: the body sets the algebra by
   `letI := (f.appLE V U e).hom.toAlgebra`, with R = Γ(S,V) and A = Γ(X,U).
   Read Scheme.Hom.appLE: it is f's section map followed by restriction to U.
   Read Spec and Spec.map in Scheme.lean and Spec.homEquiv in
   GammaSpecAdjunction.lean: spectra are contravariant, as the spectrum dependency
   requires. No independent algebra structure is assumed. Verdict: exact.
7. That map is of finite type: `∃ hft : Algebra.FiniteType Γ(S,V) Γ(X,U)` and
   `letI := hft`. Read Algebra.FiniteType in FiniteType.lean: the top subalgebra
   is finitely generated. This is the node's finite-generation/polynomial-quotient
   notion, including zero generators. Verdict: exact.
8. Quasi-finiteness at x's prime: the final clause is
   `Algebra.IsQuasiFiniteAtPrime Γ(S,V) Γ(X,U) (hU.primeIdealOf ⟨x,hx⟩)`.
   Read its recorded module: it contracts that prime and uses
   `PrimeSpectrum.preimageHomeomorphFiber` to identify the corresponding prime
   in `p.asIdeal.Fiber S`, then asserts its singleton is open. Read that
   homeomorphism's signature in ResidueField/Fiber.lean. The reversed tensor
   factor order is canonically equivalent, per the project's fibre-ring
   convention; the finite-type instance is the witness in item 7.
   Verdict: exact, with no replacement by Mathlib's weaker quasi-finiteness.
9. The only conclusion is local finite type: `LocallyOfFiniteType f`.
   Read its class in Morphisms/FiniteType.lean: all affine pairs have finite-type
   appLE maps. Stacks 01T2 identifies this with the node's affine-cover criterion;
   Definition 01T1 gives the pointwise form. Read the proof dependency
   HasRingHomProperty.iff_exists_appLE and its finite-type instance to confirm
   the docstring's final step. Verdict: exact; no global finite-type or
   quasi-compact conclusion added.

Edge cases: empty X makes the pointwise hypothesis vacuous and local finite type
valid; a morphism to the empty scheme forces empty X. Zero section rings cause
no exclusions: CommRing and finite generation do not assume nontriviality, and
an empty affine open need not contain any point. Zero polynomial generators are
allowed by Algebra.FiniteType. No index set, positive integer, field, or
characteristic parameter is imposed. A non-quasi-compact disjoint union of points
is not excluded. The arbitrary universe u matches the recorded dependency and
Mathlib's category of schemes; X and S must inhabit one scheme category to form
this morphism, with no independent smaller universe of test objects. All
variables and universes are explicitly bound.

Independent searches (different queries from the first worker):

- LeanFinder via msearch: `finite type follows from being quasi finite at every
  source point` returned eight hits, including LocallyQuasiFinite,
  locallyQuasiFinite_iff, locallyOfFiniteType_iff, and finite-morphism instances.
  Opening the actual Mathlib class confirms it omits local finite type; none is
  this theorem with the recorded Stacks predicate. Search-result prose was not
  used as evidence in place of the declarations.
- Loogle via msearch: `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` reports
  unknown identifier (the public index does not index the project's predicate).
  It supplies no evidence of absence by itself.
- LeanSearch via msearch: `quasi finite at all points implies finite type locally`
  is unavailable with Internal Server Error; recorded as unavailable.
- Direct rg of Mathlib AlgebraicGeometry and RingTheory, source WeilConjectures,
  project lean/Sheaf, and dag/lean_names_upstream.json for
  `IsLocallyQuasiFinite|quasiFinite.*finiteType|finiteType.*quasiFinite|locallyOfFiniteType_of_isLocallyQuasiFinite`
  found the recorded predicate, its use in QuasiFiniteLocusOpen, and a ring
  Zariski-main-theorem occurrence in a different direction. No existing exact
  theorem or name collision. The existing project predicate is imported rather
  than copied.

No mismatches found; no Lean or node changes were necessary. There are no new
nodes, dependency modules, or statement corrections to audit. The single direct
import supplies both hypothesis and conclusion. The sole theorem has a `sorry`
proof, no definitions or auxiliary proved results are added, both docstrings
carry the source and blueprint identifier, and the theorem docstring follows
both DAG proof steps. The node's lean.statement is verbatim the file signature.
Second reading changed only this report.

Second-reader validation: scompile completed successfully (1.6 seconds, exit 0,
no warnings). deliver2 --no-push printed OK: preflight passes and compiles.
