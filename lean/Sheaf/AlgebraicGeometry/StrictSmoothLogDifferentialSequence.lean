/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ChartLogSmoothDeformationCalculus
public import Sheaf.AlgebraicGeometry.EtaleTensorSectionsModule
public import Sheaf.AlgebraicGeometry.IntegralChartLogificationThickening
public import Sheaf.AlgebraicGeometry.LogInfinitesimalLifting
public import Sheaf.AlgebraicGeometry.LogMorphismOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.TangentBundle
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres

/-! # Strict smooth logarithmic differential sequences

Source: the DAG's agent-formulated strict smooth sequence; Kato (1988), §3;
ILO, Exposé X Proposition 1.2, p.138, and XVI Proposition 3.6.3, p.252 (context).
(blueprint: lem-per-strict-smooth-log-differential-sequence)

The ordinary target is the canonical module extension, identified with the
recorded tensor-sections étale sheaf by the published normalized comparison. Its
derivation is specified by naturality, the derivation identities,
base vanishing, and agreement with the recorded universal Zariski derivation.
These conditions determine its extension to étale test objects uniquely: for an
étale algebra, a derivation extends uniquely from the base. No map or differential
sheaf is supplied as a hypothesis.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
namespace EtaleLogMap

/-- Characterization of the ordinary universal derivation on the small étale site.
The additive maps are natural, satisfy Leibniz, kill all relative base sections,
and agree on source opens with `relativeDifferentialsDerivation`, through the
canonical tensor-extension adjunction unit. Étale algebras have unique
extensions of derivations, so this specifies the usual ordinary differential of
every local function, including on non-Zariski étale test objects.
Source: the item's ordinary-differential convention; Stacks 01UM and 03DU
(blueprint: lem-per-strict-smooth-log-differential-sequence). -/
def IsOrdinaryEtaleDifferential {Z W : Scheme.{u}} (c : Z ⟶ W)
    (d : ∀ V : Z.Etale, Γ(V.left, ⊤) →+
      (etaleTensorSectionsModule c.relativeDifferentials).val.obj (op V)) : Prop :=
  (∀ (V : Z.Etale) (a b : Γ(V.left, ⊤)),
    d V (a * b) = a • d V b + b • d V a) ∧
  (∀ (V V' : Z.Etale) (k : V' ⟶ V) (a : Γ(V.left, ⊤)),
    (etaleTensorSectionsModule c.relativeDifferentials).val.map k.op (d V a) =
      d V' (k.left.appTop a)) ∧
  (∀ (V : Z.Etale) (U : W.Etale) (k : V.left ⟶ U.left)
    (_hk : k ≫ U.hom = V.hom ≫ c) (a : Γ(U.left, ⊤)), d V (k.appTop a) = 0) ∧
  ∀ (O : Z.Opens) (a : Γ(Z, O)),
    d (Scheme.Etale.mk O.ι) (Z.restrictFunctorΓ.inv.app (op O) a) =
      ((((Classical.choose scheme_zariski_etale_quasiCoherent_equivalence) Z).adjunction.unit.app
        c.relativeDifferentials).app O)
          (c.relativeDifferentialsDerivation.d (X := op O) a)

/-- The specified arrows of the sequence. The pullback unit represents `1 ⊗ s`;
linearity then fixes its value on every pure tensor. The second arrow is fixed on
all ordinary and logarithmic symbols, with the unit formula written explicitly.
Source: the displayed maps in the item's statement; ILO X 1.2 (context)
(blueprint: lem-per-strict-smooth-log-differential-sequence). -/
def DifferentialSequenceMaps {Z W S : Scheme.{u}}
    {L : EtaleLogStructure Z} {M : EtaleLogStructure W} {N : EtaleLogStructure S}
    (c : EtaleLogMap L M) (g : EtaleLogMap M N)
    (hp : (smallEtaleModulePushforward c.base).IsRightAdjoint)
    (d : ∀ V : Z.Etale, Γ(V.left, ⊤) →+
      (etaleTensorSectionsModule c.base.relativeDifferentials).val.obj (op V))
    (i : (smallEtaleModulePullback c.base hp).obj (differentialSheaf g) ⟶
      differentialSheaf (c.comp g))
    (p : differentialSheaf (c.comp g) ⟶
      etaleTensorSectionsModule c.base.relativeDifferentials) : Prop :=
  (∀ (U : W.Etale) (a : Γ(U.left, ⊤)),
    i.val.app (op ((MorphismProperty.Over.pullback @Etale ⊤ c.base).obj U))
      (((smallEtaleModuleAdjunction c.base hp).unit.app (differentialSheaf g)).val.app
        (op U) (sheafD g U a)) =
      sheafD (c.comp g)
        ((MorphismProperty.Over.pullback @Etale ⊤ c.base).obj U)
        ((pullback.fst U.hom c.base).appTop a)) ∧
  (∀ (U : W.Etale) (m : M.monoidSheaf.obj.obj (op U)),
    i.val.app (op ((MorphismProperty.Over.pullback @Etale ⊤ c.base).obj U))
      (((smallEtaleModuleAdjunction c.base hp).unit.app (differentialSheaf g)).val.app
        (op U) (sheafDLog g U m)) =
      sheafDLog (c.comp g)
        ((MorphismProperty.Over.pullback @Etale ⊤ c.base).obj U)
        (c.sectionMap U ((MorphismProperty.Over.pullback @Etale ⊤ c.base).obj U)
          (pullback.fst U.hom c.base) pullback.condition m)) ∧
  (∀ (V : Z.Etale) (a : Γ(V.left, ⊤)),
    p.val.app (op V) (sheafD (c.comp g) V a) = d V a) ∧
  (∀ (U : W.Etale) (V : Z.Etale) (k : V.left ⟶ U.left)
    (hk : k ≫ U.hom = V.hom ≫ c.base) (m : M.monoidSheaf.obj.obj (op U)),
    p.val.app (op V) (sheafDLog (c.comp g) V (c.sectionMap U V k hk m)) = 0) ∧
  ∀ (V : Z.Etale) (m : L.monoidSheaf.obj.obj (op V)) (v : Γ(V.left, ⊤)ˣ),
    L.alpha.app (op V) m = v.val →
      p.val.app (op V) (sheafDLog (c.comp g) V m) =
        (↑(v⁻¹) : Γ(V.left, ⊤)) • d V v.val

/-- A local splitting with the specified arrows, on an étale cover.
Both inverse identities and the four inclusion/projection identities are stated,
so this is a splitting of this sequence, not just an isomorphism of its objects.
Source: the item's local splitting clause and proof Steps 1--3
(blueprint: lem-per-strict-smooth-log-differential-sequence). -/
def DifferentialSequenceLocallySplit {Z : Scheme.{u}} {A B D : SmallEtaleModules Z}
    (i : A ⟶ B) (p : B ⟶ D) : Prop :=
  ∀ z : Z, ∃ V : Z.Etale, z ∈ Set.range V.hom ∧
    ∃ (r : B.over V ⟶ A.over V) (s : D.over V ⟶ B.over V),
      i.over V ≫ r = 𝟙 _ ∧ s ≫ p.over V = 𝟙 _ ∧
      s ≫ r = 0 ∧ i.over V ≫ p.over V = 0 ∧ r ≫ i.over V + p.over V ≫ s = 𝟙 _

/-- For a strict log morphism with smooth underlying scheme map, the canonical
logarithmic transitivity sequence is short exact and locally split. For an étale
underlying map its specified first arrow is an isomorphism. The schemes are
arbitrary and the three log structures are fine, with no Noetherian hypothesis.

Source: the DAG's agent-formulated sequence; Kato (1988), §3 (transitivity, 3.12),
referenced in ILO X Proposition 1.2, p.138, and XVI Proposition 3.6.3, p.252;
ILO gives context rather than this sequence verbatim.
(blueprint: lem-per-strict-smooth-log-differential-sequence).

Proof:
1. Apply [lem-sfb-smooth-differential-transitivity-short-exact] to c and g.
   The ordinary quotient D = Omega(Z/W) is finite locally free by
   [lem-ag-smooth-relative-differentials-finite-locally-free] and
   [def-sc-finite-locally-free-sheaf]. On a neighbourhood lift a finite basis
   through the ordinary quotient to obtain B = A direct-sum D. Transport this
   splitting to étale modules with
   [lem-trf-scheme-zariski-etale-quasi-coherent-equivalence] and normalize the
   derivations with [lem-sfb-scheme-etale-relative-differentials-comparison].
2. Strictness and [lem-per-strict-log-differentials-pushout] identify the middle
   log sheaf with P = (B direct-sum C)/image(u,-v), where C = c*omega(g).
   The specified first map sends e to [(0,e)]. This requires no Noetherianity.
3. Write b = u(a)+s(d). The map [(b,e)] to (e+v(a),d) is unchanged by adding
   (u(a'),-v(a')). Its inverse sends (e,d) to [(s(d),e)]. The maps are linear
   and restriction compatible. They identify i and p with inclusion and
   projection, giving the stated split identities and exactness. C need not
   be flat. The symbol formulas identify the maps with the asserted ones.
4. The relation dt = t dlog(t) gives the displayed unit formula. If c is étale,
   [lem-weil-pbc-etale-smooth-zero-dimensional-fibres] gives smoothness, and
   [lem-sfb-etale-localization-relative-differentials], applied to the identity
   map of W, gives D = 0. The local decomposition makes i invertible, and
   uniqueness of its inverse glues the local inverses. -/
theorem strictSmooth_logDifferentialSequence {Z W S : Scheme.{u}}
    (L : EtaleLogStructure Z) (M : EtaleLogStructure W) (N : EtaleLogStructure S)
    (hL : L.IsFine) (hM : M.IsFine) (hN : N.IsFine)
    (c : EtaleLogMap L M) (g : EtaleLogMap M N) (hc : c.IsStrict) [Smooth c.base] :
    ∃ (hp : (smallEtaleModulePushforward c.base).IsRightAdjoint)
      (d : ∀ V : Z.Etale, Γ(V.left, ⊤) →+
        (etaleTensorSectionsModule c.base.relativeDifferentials).val.obj (op V))
      (i : (smallEtaleModulePullback c.base hp).obj (differentialSheaf g) ⟶
        differentialSheaf (c.comp g))
      (p : differentialSheaf (c.comp g) ⟶
        etaleTensorSectionsModule c.base.relativeDifferentials),
      IsOrdinaryEtaleDifferential c.base d ∧ DifferentialSequenceMaps c g hp d i p ∧
      Mono i ∧ Epi p ∧
      (∃ h : i ≫ p = 0, (ShortComplex.mk i p h).Exact) ∧
      DifferentialSequenceLocallySplit i p ∧ (Etale c.base → IsIso i) := by
  sorry

end EtaleLogMap
end AlgebraicGeometry
