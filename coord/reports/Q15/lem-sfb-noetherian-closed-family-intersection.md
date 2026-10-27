## Worker report

Item: `lem-sfb-noetherian-closed-family-intersection`, group Q15, stage 2.

The module `Sheaf.AlgebraicGeometry.NoetherianClosedFamilyIntersection` states
`AlgebraicGeometry.noetherian_closed_family_intersection` and
`AlgebraicGeometry.noetherian_closed_family_tail`. Both proofs are `by sorry`.
There are no new definitions, dependency repairs, or statement corrections.
Only the existing item's `lean` field changes. Its recorded `statement` is the
main theorem's signature verbatim; `lean.declarations` also lists the tail clause.

The source statements and seven proof steps were read in the node. For the
source-based scheme structures and universal property I read Stacks
`schemes.tex`, lemma-characterize-closed-subspace (01HP, lines 415ff),
`morphisms.tex`, definition-scheme-theoretic-intersection-union (0C4H,
lines 516ff), and `coherent.tex`, lemma-acc-coherent (01Y8, lines 2549ff).
01Y8 itself treats sequences; the arbitrary-family finite-generator argument
is explicitly supplied by this node's proof. The Bourbaki archival scan is
recorded WANTED in the node; no claim is made to have consulted that scan.

Hypothesis and conclusion correspondence:

- S is a Noetherian scheme: `{S : Scheme.{u}}`, `[IsLocallyNoetherian S]`,
  `[CompactSpace S]`, exactly the two hypotheses in the node's definition.
- The open immersion v:V -> S is `(v : V ⟶ S) [IsOpenImmersion v]`.
  V is not required to be an affine, separated or nonempty scheme.
- The set-indexed family of quasi-coherent ideal sheaves is
  `{L : Type w} (I : L → V.IdealSheafData)`. The recorded ideal-sheaf
  interface is `IdealSheafData`, so quasi-coherence of the input is encoded
  by that type rather than imposed as a second assumption. The family index
  universe w is independent of the scheme universe u.
- C_l is `(I l).subscheme` with immersion `(I l).subschemeι`.
  These are Mathlib's actual closed subschemes, with kernel I_l, rather than
  arbitrary chosen closed schemes. Any closed immersion with the specified
  ideal sheaf represents the same closed subscheme, so using this fixed
  representative does not restrict the node's family.
- The sheaf sum is the existentially named `J` constrained by
  `J = (⨆ l, I l)`. This is the existing complete-lattice supremum, not a
  private construction. `J.toModules.IsQuasicoherent` explicitly states
  quasi-coherence of the associated actual module sheaf.
- On every affine A, `J.ideal A = ⨆ l, (I l).ideal A` gives the sum-of-section-
  ideals formula. `Nonempty (J.toModules.restrict A.2.fromSpec ≅ tilde
  (ModuleCat.of Γ(V,A) ↥(⨆ l, (I l).ideal A)))` states the claimed tilde
  presentation on Spec Γ(V,A). The ideal's carrier is explicitly coerced
  to a type; no quotient or summand module is substituted for the ideal.
- A finite subset L_0 is `L₀ : Finset L`, with
  `J = (⨆ l ∈ L₀, I l)`. Ideal sums are suprema in the existing ideal lattice.
- For L = {d in N : m <= d}, the second theorem uses exactly the subtype
  `{d : ℕ // m ≤ d}`. It supplies `N : ℕ`, `m ≤ N`, and equality of the
  full sum with the sum indexed by `{d : ℕ // m ≤ d ∧ d ≤ N}`. The final
  implication `((⨆ d, I d) = ⊥ → N = m)` explicitly includes the zero-sum
  choice N = m. It uses the same S, V, v and Noetherian hypotheses.
- The required Z and i are `J.subscheme` and `J.subschemeι`. The theorem
  includes `IsClosedImmersion J.subschemeι` and `J.subschemeι.ker = J`.
- On each affine A, the square
  `IsPullback (J.subschemeCover.f A) (J.glueDataObjι A)
    J.subschemeι A.1.ι`
  gives the quotient chart over A, including the actual quotient ring map.
  The source of `subschemeCover.f A` is definitionally
  `Spec (.of (Γ(V,A) ⧸ J.ideal A))`; the preceding affine ideal equality
  identifies this with the node's quotient by the sum of the I_l(A).
- Arbitrary test schemes and maps are `∀ (T : Scheme.{u}) (t : T ⟶ V)`.
  There is no instance or reducedness, finiteness or Noetherian hypothesis
  on T. All schemes lie in a common arbitrary universe u, as required for
  morphisms in the category of schemes; this is not a finiteness condition.
- Unique factorization through Z is
  `∃! a : T ⟶ J.subscheme, a ≫ J.subschemeι = t`. Its first equivalence
  is exactly factorization through each C_l. Its second equivalence says
  that for every l, affine A of V, affine W of T and inclusion
  `h : W.1 ≤ t ⁻¹ᵁ A.1`, the ideal `(I l).ideal A` lies in the kernel
  of the actual induced ring map `(t.appLE A.1 W.1 h).hom`.
- The immersion of finite type v o i is rendered by
  `IsImmersion (J.subschemeι ≫ v)`, `LocallyOfFiniteType` of the same
  composite, and `QuasiCompact` of that composite. The last two predicates
  are exactly the recorded finite-type convention.
- For each affine B of S, the final clause gives finitely many elements
  `f : Fin n → Γ(S,B)` and affine opens `A : Fin n → V.affineOpens`.
  It explicitly identifies A_j with v^{-1}D(f_j), places D(f_j) in the
  image of V, and states `⨆ j, S.basicOpen (f j) = v.opensRange ⊓ B.1`.
  Thus the principal opens themselves cover V intersect B.
- The displayed `@IsLocalization.Away` uses the algebra induced by
  `(v.appLE B.1 (A j).1 (hAB j)).hom`; it identifies Γ(V,A_j) as R_{f_j}
  over R = Γ(S,B), without an arbitrary ring-map choice or an extra hypothesis.
- The quotient charts are the actual `J.subschemeCover.f (A j)`.
  Their open ranges have supremum exactly
  `(J.subschemeι ≫ v) ⁻¹ᵁ B.1`, and their squares over A_j are pullbacks.
  Equivalently these give the asserted affine cover of Z x_S B.
  Their source rings are Γ(V,A_j)/J(A_j), hence the stated R_{f_j}/I(D(f_j))
  by the localization and ideal formulas already included.

Dependency declarations read and used:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`, its full component_noetherian
  signature and the affine-cover equivalences; imported publicly.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`,
  `CompactSpace` and its isCompact_univ field; available publicly through
  Noetherian. No Hausdorff assumption is included.
- `pqf-def-coherent`: the recorded
  `Sheaf.AlgebraicGeometry.CoherentFiniteType`, read in full and imported
  publicly, exposes `SheafOfModules.IsQuasicoherent`. I use quasi-coherence
  alone, not its stronger `IsQuasiCoherentFiniteType` conjunction.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; its locally-ringed-space definition
  was read and is exposed through Noetherian.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`; `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
  supplies `IsImmersion`; these are exposed through Noetherian.
- `def-sbc-closed-immersion-ideal-sheaf`: `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`,
  `AlgebraicGeometry.Scheme.Hom.ker`, including its affine formula and the
  distinction between arbitrary morphisms and quasi-compact ones.
  `IdealSheafData`, `ideal_iSup`, `subscheme`, `subschemeι`, `subschemeCover`,
  and `glueDataObjι` were read in Basic/Subscheme. Their defining data give
  the input notions, sum and quotient charts without new helper definitions.
- The actual module sheaf is the existing
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`,
  `Scheme.IdealSheafData.toModules` (kernel of the actual structure-sheaf map);
  its inclusion, affine range formula, and full docstrings were read.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and Morphisms.QuasiCompact,
  `AlgebraicGeometry.QuasiCompact`; their full fields were read.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`, `AlgebraicGeometry.tilde`,
  and `Scheme.Modules.restrict` give the affine tilde statement.
- The stated proof dependency
  `WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`
  is a plain proof import. All other proof dependencies already have
  Mathlib matches exposed by the imports; no absent proof statement was invented.

Searches for an existing whole statement (2026-10-24; wrapper output is in
`searches.jsonl`):

- msearch leanfinder: "An arbitrary sum of quasi coherent ideals on a Noetherian
  scheme equals a finite subsum and defines the universal intersection of closed
  subschemes". Eight hits: IdealSheafData complete lattice/supremum declarations,
  ideal_iSup, ideal_sSup, support_iSup, support_sSup, ideal_biInf. None states
  finite stabilization together with the universal and chart clauses.
- msearch loogle: `AlgebraicGeometry.Scheme.IdealSheafData`. Twelve hits for
  the structure and its lattice/ring instances; no whole-statement match.
- msearch leansearch: "A sum of ideal sheaves on a noetherian scheme is a finite
  subsum". Eight hits including Ideal.sum_eq_sup, Ideal.add_eq_sup and
  IdealSheafData, but no scheme-level finite-subsum theorem matching this node.
- msearch grep: `ideal_iSup|finite.*[sS]up|[sS]up.*finite|subschemeCover`,
  directory AlgebraicGeometry/IdealSheaf. Seven hits for ideal_iSup and
  subschemeCover, with its range and composite formulas. Inspected the sources.
- rg of both lean/WeilConjectures and lean/Sheaf for
  `closed.family|finite.subsum|ideal_iSup|lem-sfb-noetherian-closed-family-intersection`:
  sum ingredients and unrelated finite coproduct results; no statement of this node.
  A subsequent name-clash search in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json for the new module/declaration names returned no hits.
- The source's blueprint-id search gave no existing declaration for the item.

Edge cases: empty L gives bottom ideal, Z = V up to the canonical isomorphism,
empty finite subset, and the vacuous universal family condition. Empty V admits
empty chart covers (`n = 0`) even when S is nonempty. The unit ideal gives the
empty Z, with factorization only from the empty test scheme. Zero tail sums
allow N = m even for m = 0. Infinite L has no enumerability assumption and its
universe is not restricted. For T = Spec(k[e]/e^2), the kernel criterion retains
nilpotents and so tests scheme-theoretic rather than set-theoretic factorization.
No disputed statement or node fault remains.

Validation: prescribed scompile.py compiles this module in both sandbox and actual
library module modes, with no error or warning. Every theorem proof remains sorry.

## Second reading by Q15

I reopened the node and module for a fresh clause-by-clause pass after drafting.
This is an in-session second pass; the dispatcher brief prohibits starting another
agent, and the maintainer supplies the independent review of this delivery.

The pass checked the two Noetherian hypotheses, the open immersion, arbitrary
set-indexed family, the sum and affine tilde formula, finite subset, the tail
interval and zero bound, the closed immersion with its exact kernel, the quotient
pullback squares, both arbitrary-test equivalences, the immersion and both
finite-type predicates, and the finite principal/localization/quotient covers.

I corrected the initial chart formulation: intersecting every D(f_j) with V
would not by itself say D(f_j) lies in V. The delivered clause explicitly
requires each D(f_j) to lie in v.opensRange and their union to be V intersect B.
This restores the node's precise principal-open cover rather than weakening it.
The affine chart statement names the actual quotient square, so an abstract
isomorphism of affine schemes cannot lose the map to the ambient open.
The affine-test criterion uses the actual appLE map on every eligible affine
chart W of T, with no reduction or Noetherian assumption on T.
The tail theorem indexes the interval by a subtype with both endpoint inequalities,
and includes the forced choice N = m in the zero case. No other mismatch found.

Compiler corrections were the Mathlib namespace `AlgebraicGeometry.tilde` and an
explicit carrier coercion of the supremum ideal in ModuleCat.of. Neither changes
the mathematical statement. Both delivered declarations carry the same owning
blueprint id and complete proof explanations; no helper theorem lacks a node.
