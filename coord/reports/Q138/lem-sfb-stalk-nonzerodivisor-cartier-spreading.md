## Worker report

The module `Sheaf.AlgebraicGeometry.StalkNonzerodivisorCartierSpreading` states the
ring and scheme clauses of lem-sfb-stalk-nonzerodivisor-cartier-spreading in two
named theorems. Both proofs are exactly `sorry`; there are no new definitions or
helper proof obligations. The node changes only in `lean`.

Source read: literature/stacks-project/divisors.tex, Tag 0AG8,
lemma-effective-Cartier-in-points, statement (2) and proof, lines 2939--2980.
The node expands the denominator argument and the finite annihilator argument;
these are reproduced step by step in the theorem docstrings. No statement
correction is needed. The source's hypothesis on points of the closed subscheme
is stated by the node equivalently on every ambient point, with unit generators
on the complement.

Ring hypothesis and conclusion correspondence:

- A commutative Noetherian ring B: `{B : Type u} [CommRing B]
  [IsNoetherianRing B]`.
- An ideal I and prime ideal p: `(I p : Ideal B) [p.IsPrime]`.
- The localized element t: `(t : Localization.AtPrime p)`.
- The equality I B_p = (t): `hI : I.map (algebraMap B
  (Localization.AtPrime p)) = Ideal.span {t}`. Ideal extension is `Ideal.map`,
  not the set image of the ideal.
- Multiplication by t injective: `ht : Function.Injective
  (fun z : Localization.AtPrime p ↦ t * z)`.
- There is a denominator outside p: `∃ g : B, g ∉ p ∧ ...`.
- There is a numerator belonging to the original ideal: `∃ a : B, a ∈ I ∧ ...`.
- I B_g = (a/1): `I.map (algebraMap B (Localization.Away g)) =
  Ideal.span {algebraMap B (Localization.Away g) a}`.
- Multiplication by a/1 on B_g is injective: the final `Function.Injective`
  on `fun z : Localization.Away g ↦ algebraMap B (Localization.Away g) a * z`.
  In particular the conclusion retains the numerator in I, not just an arbitrary
  generator somewhere in the localization.

Scheme hypothesis and conclusion correspondence:

- Locally Noetherian ambient scheme: `{X H : Scheme.{u}}
  [IsLocallyNoetherian X]`. No global Noetherianity or quasi-compactness is imposed.
- Closed subscheme H of X: `(i : H ⟶ X) [IsClosedImmersion i]`.
- Its quasi-coherent ideal sheaf: the recorded construction `i.ker`.
- At every x: `h : ∀ x : X, ...`.
- Its stalk as an ideal of O_{X,x}: `(i.ker.ideal U).map
  (X.presheaf.germ U.1 x hx).hom`, for an affine neighbourhood `U` containing x.
  Quasi-coherence identifies this ideal extension with the image of the actual
  ideal-module stalk in the structure-sheaf stalk. The affine germ map presents
  O_{X,x} as localization at the prime of x; this is the same presentation used
  by the parent SNCBoundaryParameterCriterion module. Existence of such a chart
  adds no mathematical hypothesis, and the ideal is independent of the chart.
- A generator of that ideal: `∃ (U : X.affineOpens) (hx : x ∈ U.1)
  (t : X.presheaf.stalk x), ... = Ideal.span {t} ∧ ...`.
- Nonzerodivisor generator: `Function.Injective
  (fun z : X.presheaf.stalk x ↦ t * z)`.
- Effective Cartier ideal: `i.ker.IsInvertible`, whose upstream definition is
  exactly `∀ x, ∃ U, x ∈ U.1 ∧ (i.ker.ideal U).IsRegularPrincipal`.
- The clauses permitting 1 off H, empty H, and empty X are retained: no t is
  required to be a nonunit, no ideal is required to be proper or nonzero, and no
  scheme is assumed nonempty. There is no reducedness, integrality or regularity
  hypothesis anywhere in either statement.

Dependency declarations read and used:

- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`, with
  `Ideal.IsRegularPrincipal` read in
  `WeilConjectures.Mathlib.RingTheory.Ideal.RegularPrincipal`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `AlgebraicGeometry.Scheme.Hom.ker` and `Hom.ker_apply`; the former is publicly
  available through the closed-immersion import.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` (the recorded general module stalk
  construction, using Mathlib's stalk carrier). The ideal-inside-ring formulation
  uses the canonical ring stalk and affine germ map directly, rather than
  introducing a second stalk construction or requiring a chosen module isomorphism.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`; its ring
  structure and algebraMap come through `Mathlib.RingTheory.Localization.Away.Basic`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.

The stated proof dependencies are imported without `public`: localized ideal
membership from `Mathlib.RingTheory.Localization.Ideal`; affine closed-subscheme
constructions from `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`; the affine
module germ theorem from
`WeilConjectures.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`; and
basic-open module localization from
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
Affine ring stalk localization is already publicly available through the scheme
imports. There is no missing proof-dependency module and no import-cycle omission.

Edge cases checked mathematically before drafting: a unit generator gives the
unit ideal and injective identity multiplication; the zero ideal at a genuine
prime cannot satisfy the hypothesis since B_p is nontrivial; the zero ring has
no prime, and so is not silently excluded by an extra Nontrivial assumption.
An empty generating list in the denominator argument gives product 1. A
localization map is allowed to have a kernel. The nonreduced ring of dual numbers
with the unit ideal is covered; no reducedness assumption has entered. For empty
H its ideal is the unit ideal everywhere. For empty X the pointwise hypothesis
and Cartier condition are both vacuous. The universes and all variables are
explicitly bound, with `autoImplicit false`.

Searches performed (2026-10-24):

- msearch leanfinder: "A locally Noetherian scheme with a closed subscheme whose
  ideal stalk is generated by a nonzerodivisor is an effective Cartier divisor.
  A regular generator of a localized ideal spreads to a principal open neighborhood."
  Eight hits, including basic-open denominator lemmas and IdealSheafData
  constructors; none states either complete clause.
- msearch loogle: `"Ideal", "IsInvertible"`: zero hits.
- msearch grep: `stalkIdeal|idealStalk|[Cc]artier|[Rr]egular[Pp]rincipal`,
  AlgebraicGeometry: zero Mathlib hits.
- msearch leansearch: "An ideal in a Noetherian ring generated by a nonzerodivisor
  at a prime is generated by a regular element after localizing away from some
  element outside the prime." Eight hits, including Localization.AtPrime,
  regular sequence localization and LocalizedModule.exists_subsingleton_away;
  none states the desired ideal-generator conclusion.
- rg over live WeilConjectures and Sheaf sources for the item id, stalk Cartier
  predicates, regular-principal stalk predicates, and proposed declaration names.
  No exact statement or name collision. The existing
  `Ideal.exists_notMem_isRegularPrincipal_map_away` in RegularPrincipal.lean was
  read in full: it assumes `[IsDomain Ap]` and only asserts local regular
  principality, so it cannot replace the present statement on arbitrary local
  rings with a regular generator and a specified numerator in I. RelativeEffectiveCartier
  has geometric special cases, not this general stalk criterion. The helper
  HilbertSamuel.stalkIdeal in MarkedIdealOrder was inspected; it takes the supremum
  of the same affine germ extensions. No new stalk-ideal definition is introduced.

Validation: every compile uses the prescribed scompile.py wrapper; dry-run and
push use deliver2.py. Compiler and preflight results are recorded below.

## Second reading by Q138

Re-read the node statement alongside both complete theorem signatures. The first
signature preserves the actual element t in B_p, the equality of extended ideals,
and injective multiplication, and returns g outside p and a in I with both
promised properties in B_g. The second uses a closed immersion into a locally
Noetherian scheme and quantifies over every ambient point. Its affine chart
occurs only in the presentation of the stalk ideal; it does not assume a
neighbourhood equation. The conclusion unfolds to local regular principality,
not merely a locally principal ideal or a line bundle. Empty schemes and unit
stalk ideals remain included. No mismatch requiring a node change was found.
This second pass is by the assigned worker; the independent maintainer review
reads the delivered node and module. No additional agent was started.

Validation results: scompile.py exited 0 with no compiler diagnostics for the
sandbox and library module. The deliver2.py --no-push dry run printed
`OK (dry run): commit c14da74b17f passes the preflight and compiles; nothing pushed`.
A final sandbox audit confirms only the item's `lean` field changes, the recorded
signature is verbatim, all Lean lines are at most 100 characters, and the two
named theorems each have exactly the requested `sorry` proof.
