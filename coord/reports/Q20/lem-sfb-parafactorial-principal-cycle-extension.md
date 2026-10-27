## Worker report

The theorem `AlgebraicGeometry.Scheme.LocallyFiniteWeilCycle.isPrincipalAt_of_punctured_triviality`
in `Sheaf.AlgebraicGeometry.ParafactorialPrincipalCycleExtension` states the item without changing
its mathematical statement. Its proof is `sorry`. The auxiliary definition module has real data
and no postponed theorems. Every universe and variable is explicitly bound; autoImplicit is false.

Hypotheses and clauses, matched against the complete node:

- A scheme, locally Noetherian and normal: `{X : Scheme.{u}} [IsLocallyNoetherian X]`, and
  `hX : ∀ x, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
  Normality is the recorded normal-domain condition at every stalk, without a global domain or
  irreducibility condition. No compactness or separatedness condition is imposed.
- An arbitrary set of points: `T : Set X`, with no topological predicate on T.
- The locally finite formal sum: `D : LocallyFiniteWeilCycle X`. Its `coeff : X → ℤ` gives n_D
  directly, with `codimension_one` forcing zero away from local dimension one. For each nonzero
  term its closed subset is `closure {z}`. Every such subset is nonempty, irreducible, closed and
  has generic point z; scheme sobriety and T0 give the converse and distinctness. This uses no
  choice of an indexing set and omits zero terms. The family of closures, indexed by nonzero
  terms, satisfies Mathlib `LocallyFinite`, which says each point has a neighbourhood meeting
  finitely many family members. Replacing that neighbourhood by an open neighbourhood is
  equivalent. Global finite support would exclude permitted examples and is not required.
- `R_x` is `X.presheaf.stalk x`, and `K_x` is its `FractionRing`. In `IsPrincipalAt`, the witness
  `a : (FractionRing (X.presheaf.stalk x))ˣ` is exactly a nonzero field element. Domain and
  integral-closure proofs are supplied explicitly from hX; these introduce no further hypothesis.
- Height-one primes use `Ring.WeilHeightOnePrime`, the existing nonzero-prime/no-intermediate-
  prime definition. In a domain this is exactly height one. The point z_q is the actual canonical
  image `(X.fromSpecStalk x) q.val`. The existing `Ring.weilFractionOrder` computes v_q as the
  numerator order minus the denominator order, with local length orders. On a Noetherian normal
  local domain these localizations are DVRs, so this is exactly the normalized valuation of the
  node. All height-one primes are quantified over, including those with coefficient zero.
- The parafactorial hypothesis is `hpunctured`: for every x with
  `2 ≤ ringKrullDim (X.presheaf.stalk x)` and `Disjoint (closure {x}) T`, every module L on
  `(puncturedSpectrum (X.presheaf.stalk x)).toScheme` satisfying `L.IsInvertible` has
  `Nonempty (L ≅ SheafOfModules.unit _)`. The reused puncturedSpectrum is the open complement
  of the closed point/maximal ideal. The reused IsInvertible means locally free rank one, and
  `SheafOfModules.unit` is its structure sheaf as a module. Quasi-coherence follows from that
  local triviality. The closure here is in X, not in an affine neighbourhood.
- Principality on T is `hT : ∀ x, x ∈ T → D.IsPrincipalAt x (hX x).1 (hX x).2`.
  The conclusion is the same predicate at every x of X, with no global rational equation asked for.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Noetherian: `IsLocallyNoetherian` and its Noetherian stalk instance.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: `IsDomain`, `IsIntegrallyClosed`, as
  recorded for def-weil-pbc-normal-ring (a normal scheme has normal-domain stalks).
- Mathlib.Topology.Irreducible: `IsIrreducible`, `irreducibleComponents`; Mathlib.Topology.Sober:
  `IsGenericPoint`. Generic-point indexing of closures agrees with these exact definitions.
- Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim`.
- Mathlib.RingTheory.Localization.AtPrime.Basic: `Localization.AtPrime`.
- Mathlib.RingTheory.DiscreteValuationRing.Basic: `IsDiscreteValuationRing`.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: `Scheme.Modules.IsInvertible`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`, used by the open-subscheme encoding.
- WeilConjectures.AlgebraicGeometry.PuncturedCurveBranches: `puncturedSpectrum`, the existing
  complement-of-closed-point open. Reused without a second puncture definition.
- Sheaf.RingTheory.HeightOneFractionOrder: `Ring.weilFractionOrder`; its public dependency
  Sheaf.RingTheory.WeilDivisorClassGroup supplies `Ring.WeilHeightOnePrime` and `Ring.weilOrder`.
- WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism, built on Mathlib's
  `Scheme.fromSpecStalk`: canonical point map and its generization/stalk interpretation.

The theorem also has plain imports for the stated proof dependencies: RegularNormalDecomposition,
Properties, FunctionField, LocalProperties.IntegrallyClosed, Localization.Submodule,
Localization.LocalizationLocalization, LocalizationPrimeResidueFieldIso, Regular,
Topology.NoetherianSpace, and Modules.Tilde. The large proof input
lem-per-divisorial-fractional-module-lattices has no Lean record on the read base, so it has no
module to import. Its entire seven-step use is preserved in the theorem docstring. No proof-only
notion is substituted for the cycle definition.

Edge cases checked before writing:

- Empty X: no points or nonzero coefficients; the conclusion is vacuous and the type is inhabited
  by the zero function with the elementary empty-family local-finiteness proof.
- D = 0: all required orders are zero; local equation 1 works. No nonzero-cycle assumption occurs.
- T = X: hT already gives the conclusion; hpunctured only concerns the empty possible closure
  complement. T empty: the full punctured triviality hypothesis is retained at dimension ≥ 2.
- Dimension zero: no height-one primes, witness 1; dimension one: a uniformizer to any integer
  power. Negative coefficients are retained as integers and fractions are units in the fraction
  field, with no integrality assumption on a.
- An infinite disjoint union of normal affine curves with one prime cycle on each component is
  included: the family of closures is locally finite, but is not globally finitely supported.
- Several normal components, nonseparated X and nonconstructible T remain admitted. The statement
  uses local fraction fields, not a single function field of a globally integral scheme.
- A normal singular surface with nontrivial punctured Picard group does not satisfy hpunctured
  when its singular point is eligible; the hypothesis is substantive.

Searches actually run (the new node carries complete captured output):

1. msearch leansearch: “locally finite integer coefficients codimension one cycles Weil divisors
   on a locally Noetherian scheme”. Eight hits: locally Noetherian APIs and an analytic
   meromorphic divisor. No algebraic cycle/extension theorem.
2. msearch leanfinder: “locally finite Weil divisor principal at a point normal scheme punctured
   spectrum trivial invertible modules”. Eight fraction/structure-sheaf hits. No exact statement.
3. msearch loogle: `"ClassGroup", "IsPrincipal"`. Four hits on principal fractional ideals or
   Dedekind class groups, not the scheme extension criterion.
4. msearch grep: `WeilDivisor|parafactorial|normalizedValuation`, Mathlib AlgebraicGeometry:
   zero hits. Direct rg of the project located the finite `Scheme.WeilDivisor`, the affine
   finite divisor type, `Ring.weilFractionOrder`, and the existing puncturedSpectrum.
5. rg/grep of WeilConjectures for the item id: no declaration; the RamanujamSamuelPrimeDivisor
   consumer only names this lemma in its proof docstring. Direct rg of Sheaf found no local
   principality predicate or locally finite scheme divisor. The finite WeilDivisor cannot encode
   the non-quasi-compact edge case above. It was read and not duplicated under another name.
6. DAG definition-node scan for locally finite cycles, and `blueprint_refs.py search` for
   “Weil divisor” and “codimension-one cycle”: no preexisting definition node with this notion.
   `blueprint_refs.py ancestor` returns None for this item's currently recorded ancestry; the
   new node inherits that None and prepends the item to its inherited via chain.

Sources read: Stacks divisors.tex, definition-Weil-divisor and the preceding non-quasi-compact
warning; the full dependency signatures/docstrings listed above; the online English translation
of EGA IV4 21.13.15 and its proof (downloaded and text-extracted because the browser parser rejects
its size). EGA confirms arbitrary S and global closure, with no extra compactness assumptions.
No statement correction or mathematical dispute was needed.

Validation: both delivered modules compile separately in dependency order through scompile.py,
including module-mode library compilation, under the default 60-second limit, with no errors or
unexpected warnings.

## New nodes

`def-sfb-locally-finite-principal-cycle` defines precisely the locally finite cycle and its
local-equation predicate introduced inline by the item. Its source is EGA IV4 Section 21.6 and
21.13.15 with Stacks Tag 0BE2 for local finiteness. The coefficient function, codimension property,
and locally finite family are actual structure fields; IsPrincipalAt is an explicit existential
using the existing fraction order and canonical morphism. This is needed because the current
Scheme.WeilDivisor requires globally finite support, while affine fractional-ideal notions do not
supply a global locally finite scheme cycle. Existing normalized orders, punctured spectra and
module invertibility are all reused. Its search records contain the actual msearch outputs and
additional direct project/DAG searches. The item's only change outside lean is adding this new
node to stmt_deps.

## Second reading by Q20

The dispatcher explicitly instructed this worker not to start other agents and states that the
maintainer performs the independent delivery review. Accordingly this section records a second
self-check, not a claimed independent worker review. I reopened the node and both modules and
matched every hypothesis/clause as above. In particular I checked global closure, arbitrary T,
local finiteness of closures rather than mere pointwise finite support, negative coefficients,
zero coefficients at omitted primes, nonintegral X, actual local fraction fields, the canonical
point map, all height-one primes, and an isomorphism to the structure module on the actual
punctured scheme. No mismatch was found on that second pass. The independent review remains
with the maintainer as the assignment specifies.

## Maintainer fix (second reader, 2026-10-24)

The structure `LocallyFiniteWeilCycle` duplicated Mathlib's `AlgebraicGeometry.AlgebraicCycle X ℤ`
(`@[stacks 02QR]`, `Function.locallyFinsupp X ℤ`), which the project already uses for this
notion (def-per-cartier-fraction-cover, lem-per-weil-divisor-strict-local-cartier-test). Locally
finite support is the same as local finiteness of the closures of the nonzero terms, because an
open set meets the closure of `{z}` exactly when it contains `z`. The new node's module now
defines only `AlgebraicGeometry.AlgebraicCycle.IsPrincipalAt` on Mathlib's type, with the same
body. The item takes `D : AlgebraicCycle X ℤ` with the codimension-one hypothesis
`hD : ∀ z, D z ≠ 0 → ringKrullDim (X.presheaf.stalk z) = 1`, in the same form as the existing
strict-local Cartier test. The theorem is now
`AlgebraicGeometry.AlgebraicCycle.isPrincipalAt_of_punctured_triviality`. Its hypotheses and
conclusion are otherwise unchanged. Both modules compile through nt_compile.py.
