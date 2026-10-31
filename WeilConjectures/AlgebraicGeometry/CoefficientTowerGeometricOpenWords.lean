/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerGeometricAssembly

/-! # Open normalization of the constructed geometric words

Source: Local pairs and Levels of the geometric coefficient-tower gluing proof.
(blueprint: lem-sp-geometric-open-word-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The explicit binary word has the specified ordinary open-composition boundary.
Source: Stacks 0F7J, trivial-open first compactification in the common-tower proof
(blueprint: lem-sp-geometric-open-word-normalization).

Proof: first use composition_refinement to replace the compactification a of j by
its trivial compactification (j,id). Choose the binary triangle with cf=(j,id),
cg=c and cfg=c.precomp j, with q=c.i and p=id. Its proper/open square has both
proper arrows identities. The vertical identity law for gamma cancels its two
proper identity comparisons. The remaining word is the open compositor followed
by the proper image of c.g. To identify its transport to the supplied ordinary
operations, conjugate the ordinary pull adjunctions by the fixed graph
coordinates. Their direct-image comparisons are section-pinned, hence preserve
the normalized finite adjunction units and counits. Recover the ordinary
composition comparison from o.comp_termwise and o.comp_evaluation by applying
single objects in degree zero, homology in degree zero, and faithful component
sections of ordinary systems. Thus it is the canonical pull compositor under
these coordinates. Uniqueness of its left adjoint identifies the open compositor
with the ordinary leftAdjointUniq word used by sequenceOpenComposition.
Exact derived localization preserves that identity and its naturality. Finally
cancel the intervening realization counit, producing exactly openComposition,
and restore a by refinement compatibility. The resulting first factor is the
constructed openComparison, since that definition uses precisely the comparison
to (j,id) and its proper unitor. No finite evaluation of derived maps is used to
infer equality, and the identity-open case is the proper/open identity law. -/
theorem open_words
    (pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)
    (k : Type u) [Field k] [CharP k pchar]
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (x : SpTowerShriek.OpenExchange l E b o) (laws : SpTowerShriek.Laws l E b o x)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (g : GraphCoordinates l E b o)
    : ∀ {U X Y : Scheme.{u}}
    [U.Over (Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [Y.Over (Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (a : Compactification j) (c : Compactification f) (K : C l E b q U),
    ((operations l E k b o q z g).composition j f (j ≫ f) rfl a c
      (c.precomp j)).hom.app K =
      (F l E b o q c).map
        ((openComparison l E b o q g (ambient_field k U) (ambient_field k X) j a).hom.app
          K.obj) ≫
        (openComposition l E b o q j c).hom.app K.obj := by sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
