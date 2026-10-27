module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.Topology.ClosedImmersionPushforwardExact
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.ClosedPushforwardPseudoCoherence

/-! # Relative pseudo-coherence under composition

Source: Stacks Project, More on Morphisms, Tag 09UT,
`lemma-composition-relative-pseudo-coherent`
(blueprint: lem-sfb-relative-pseudocoherence-composition).

Relative finite-stage pseudo-coherence is unchanged by composition with a base morphism
whose structure sheaf is relatively pseudo-coherent.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- If the structure sheaf of `Y` in degree zero is pseudo-coherent relative to `S`, then
an arbitrary derived object on `X` is `m`-pseudo-coherent relative to `Y` exactly when it
is `m`-pseudo-coherent relative to `S`.

Source: Stacks Project, More on Morphisms, Tag 09UT,
`lemma-composition-relative-pseudo-coherent`
(blueprint: lem-sfb-relative-pseudocoherence-composition).

Proof:
1. Choose affine opens W = Spec R covering S, affine opens V = Spec A over W covering Y,
   and affine opens U = Spec B over V covering X. By
   lem-sfb-relative-pseudocoherence-all-affine-charts and finite type, choose closed
   embeddings k : V → affine n-space over W and i : U → T = affine r-space over V.
   The polynomial surjections give closed embeddings j : T → Q = affine (n+r)-space
   over W and l = i followed by j; j is the polynomial base change of k. The integers
   n and r do not depend on the approximation degree.
2. Apply the all-affine-charts criterion to O_Y[0] in every degree. It makes O_V[0]
   pseudo-coherent relative to W. Polynomial projection is flat by
   lem-nagata-polynomial-projection-flat. Thus
   lem-sfb-relative-pseudocoherence-flat-base-change makes O_T[0] pseudo-coherent
   relative to affine r-space over W: derived pullback of the free rank-one structure
   module is the structure module. The all-affine-charts criterion now makes
   Rj_*(O_T[0]) absolutely pseudo-coherent on Q in every finite degree.
3. By lem-sc-closed-immersion-pushforward-exact, closed pushforward is exact on
   abelian sheaves, hence also on modules by retaining scalar actions on kernels and
   cokernels. Therefore its derived functor is computed termwise on any complex.
   For every open H in Q, j_*i_*F evaluated on H is F(i⁻¹j⁻¹H) = l_*F(H), with
   the same scalar action. Consequently Rj_*Ri_*(E|U) ≅ Rl_*(E|U), and step 2 is
   pseudo-coherence of the ordinary structure-module pushforward (j_*O_T)[0].
4. Apply lem-sfb-closed-pushforward-pseudocoherence to j and K = Ri_*(E|U).
   Its hypothesis is supplied by steps 2 and 3. It identifies m-pseudo-coherence of
   Ri_*(E|U) with that of Rl_*(E|U), without a bound or quasi-coherence assumption.
5. If E is relatively m-pseudo-coherent over Y, the all-affine-charts criterion and
   step 4 give m-pseudo-coherence of Rl_*(E|U); the chosen U over W and l witness
   relative m-pseudo-coherence over S. Conversely the criterion over S gives the
   property for Rl_*(E|U); step 4 gives it for Ri_*(E|U), and the covers U over V
   with i witness relative m-pseudo-coherence over Y. This works for every integer m. -/
theorem isMPseudoCoherentRelativeTo_comp_iff
    [∀ T : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType (f ≫ g)]
    (hY : IsPseudoCoherentRelativeTo g
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings Y.toRingedSpace))))
    (m : ℤ) (E : schemeDerivedCategory X) :
    IsMPseudoCoherentRelativeTo f m E ↔ IsMPseudoCoherentRelativeTo (f ≫ g) m E := by
  sorry

end AlgebraicGeometry.Scheme
