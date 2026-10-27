module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.ModuleStrictTransformFlatPullback
import Sheaf.AlgebraicGeometry.StrictTransformComparisonEpimorphism
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import WeilConjectures.Blowup.Complement
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing fibrewise finite free loci by an admissible blowup

Source: Stacks Project, More on Flatness, Tag 080Y, final paragraph;
Divisors, Tags 080M, 080N, 080A, 080I and 080F
(blueprint: lem-trf-admissible-local-free-gluing).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Package the existing admissible centre with a specified morphism for this gluing theorem.
This helper retains the centre, the quasi-compact preserved open,
and the specified identification of its morphism with that centre's blowup.
Source: Stacks Project, Divisors, Tags 080L and 080M
(blueprint: lem-trf-admissible-local-free-gluing). -/
structure AdmissibleBlowupDatum {S T : Scheme.{u}} (U : S.Opens) (b : T ⟶ S) where
  /-- The finite-type quasi-coherent centre, disjoint from the preserved open. -/
  center : IsAdmissible S U
  /-- The preserved open is quasi-compact. -/
  compact : IsCompact (U : Set S)
  /-- The specified identification with the blowup of the retained centre. -/
  iso : T ≅ center.I.blowup
  /-- The identification is over the base. -/
  over : iso.hom ≫ center.I.blowupMap = b


namespace Scheme.Modules

/-- Transport the strict transform along the specified blowup identification.
This is the existing centre-dependent strict transform, pulled back along the induced
fibre-product isomorphism; it introduces no alternative supported-section quotient.
Source: Stacks, Divisors, Tag 080D (1)
(blueprint: lem-trf-admissible-local-free-gluing). -/
noncomputable def admissibleGluingTransform {X S T : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] {U : S.Opens} {b : T ⟶ S}
    (D : AdmissibleBlowupDatum U b) : (Limits.pullback f b).Modules :=
  (tensorPullback (pullback.map f b f D.center.I.blowupMap (𝟙 X) D.iso.hom (𝟙 S)
    (by simp) (by simpa using D.over.symm))).obj
    (@moduleStrictTransform X S f D.center.I
      (D.center.I.isFiniteType_toModules_sheaf D.center.finiteType) F inferInstance)

/-- The projection-compatible inclusion of the fibre product over the open `W`
into the global fibre product. Its source is canonically the open above `W`.
Source: Stacks, Schemes, fibre products, and Divisors, Tag 0805
(blueprint: lem-trf-admissible-local-free-gluing). -/
noncomputable def admissibleGluingInclusion {X S T : Scheme.{u}} (f : X ⟶ S)
    (b : T ⟶ S) (W : S.Opens) :
    Limits.pullback (f ∣_ W) (pullback.snd b W.ι) ⟶ Limits.pullback f b :=
  pullback.lift
    (pullback.fst (f ∣_ W) (pullback.snd b W.ι) ≫ (f ⁻¹ᵁ W).ι)
    (pullback.snd (f ∣_ W) (pullback.snd b W.ι) ≫ pullback.fst b W.ι)
    (by
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, ← Category.assoc, pullback.condition, Category.assoc,
        pullback.condition])

/-- The induced map to the given local blown-up family, uniquely specified by
its source and base projections. The equation `hc` says the refinement is over `W`.
Source: Stacks, Divisors, Tags 080N and 080A
(blueprint: lem-trf-admissible-local-free-gluing). -/
noncomputable def admissibleGluingComparison {X S T Tj : Scheme.{u}} (f : X ⟶ S)
    (b : T ⟶ S) (W : S.Opens) (bj : Tj ⟶ W.toScheme)
    (c : Limits.pullback b W.ι ⟶ Tj) (hc : c ≫ bj = pullback.snd b W.ι) :
    Limits.pullback (f ∣_ W) (pullback.snd b W.ι) ⟶ Limits.pullback (f ∣_ W) bj :=
  pullback.map (f ∣_ W) (pullback.snd b W.ι) (f ∣_ W) bj
    (𝟙 _) c (𝟙 _) (by simp) (by simpa using hc.symm)

/-- Local free loci survive the common admissible refinement and unite to an open
surjective over the new base. All local blowups and refinement maps retain their
specified centre ideals and blowup identifications.
Source: Stacks, More on Flatness, Tag 080Y, final paragraph; Divisors, Tags 080M,
080N, 080A, 080I and 080F (blueprint: lem-trf-admissible-local-free-gluing).

Proof: (1) Extend each specified local centre to S, first gluing it to the unit
ideal on U and then extending the finite-type ideal from U union W_j, using
lemma-nagata-glue-finite-type-ideals and lemma-nagata-finite-type-ideal-extension-exists.
(2) Blow up the finite product of the extended centres. It is unit on U. An empty
cover forces S empty, where the unit-ideal blowup and empty good open suffice.
(3) Flat blowup base change identifies its restriction to W_j with the blowup of
the product there. The product-ideal comparison identifies the factor map c_j with
the blowup in the extension of the other factors to T_j. This ideal is finite type
and unit above U intersect W_j. The preserved open is quasi-compact since the local
blowup is an isomorphism there. Use thm-nagata-blowup-flat-base-change,
thm-nagata-blowup-product-ideal and thm-nagata-global-blowup-complement.
(4) lem-trf-module-strict-transform-flat-pullback restricts the global transform to
that of the product centre; both source and base restrictions are open immersions.
(5) The product centre's support is the union of the first centre and the image
of the second one, checked off the first centre using the complement isomorphism.
lem-trf-strict-transform-comparison-epimorphism gives the successive-to-single epi.
lem-trf-iterated-transform-exceptional-support kills its supported kernel, so it is
an isomorphism compatible with the quotient maps.
(6) Flat base change of f makes the family over T_j flat. A finite locally free
module on V_j has stalks finite direct sums of relatively flat local rings, hence
is relatively flat. lem-pc-relatively-flat-module-pullback preserves this flatness.
(7) The second blowup's exceptional ideal is Cartier by
thm-nagata-blowup-principalizes-center. lem-trf-relative-flat-cartier-support kills
supported sections of the pulled-back module. Thus its strict-transform quotient
is ordinary pullback on the inverse image of V_j, giving the claimed isomorphism.
(8) The inverse images are open, and surjective onto the restricted new bases by
lem-weil-pbc-surjective-base-change. Their union is open and surjective since W_j
cover S. Pullback preserves each finite free trivialization by the tensor formula,
so the global transform is finite locally free on that union. -/
theorem exists_admissibleBlowup_localFree_gluing
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) (hU : IsCompact (U : Set S)) (f : X ⟶ S) [Flat f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {J : Type v} [Finite J] (W : J → S.Opens)
    (hW : ∀ j : J, IsCompact (W j : Set S)) (hcover : iSup W = ⊤)
    (Tj : J → Scheme.{u}) (bj : ∀ j : J, Tj j ⟶ (W j).toScheme)
    (D : ∀ j : J, AdmissibleBlowupDatum ((W j).ι ⁻¹ᵁ U) (bj j))
    (Vj : ∀ j : J, (Limits.pullback (f ∣_ W j) (bj j)).Opens)
    (hsurj : ∀ j : J, Surjective ((Vj j).ι ≫ pullback.snd (f ∣_ W j) (bj j)))
    (hfree : ∀ j : J, SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((admissibleGluingTransform (f ∣_ W j) (F.restrict (f ⁻¹ᵁ W j).ι) (D j)).restrict
        (Vj j).ι)) :
    ∃ B : IsAdmissible S U,
      ∃ c : ∀ j : J, Limits.pullback B.I.blowupMap (W j).ι ⟶ Tj j,
      ∃ hc : ∀ j : J, c j ≫ bj j = pullback.snd B.I.blowupMap (W j).ι,
      (∀ j : J, Nonempty (AdmissibleBlowupDatum
        ((bj j) ⁻¹ᵁ ((W j).ι ⁻¹ᵁ U)) (c j))) ∧
      (∀ j : J, Nonempty
        ((tensorPullback
          (((admissibleGluingComparison f B.I.blowupMap (W j) (bj j) (c j) (hc j)) ⁻¹ᵁ
            Vj j).ι ≫ admissibleGluingInclusion f B.I.blowupMap (W j))).obj
          (@moduleStrictTransform X S f B.I
            (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance) ≅
        (tensorPullback
          (admissibleGluingComparison f B.I.blowupMap (W j) (bj j) (c j) (hc j) ∣_ Vj j)).obj
          ((admissibleGluingTransform (f ∣_ W j) (F.restrict (f ⁻¹ᵁ W j).ι) (D j)).restrict
            (Vj j).ι))) ∧
      ∃ V : (Limits.pullback f B.I.blowupMap).Opens,
        (V : Set ↥(Limits.pullback f B.I.blowupMap : Scheme.{u})) =
          ⋃ j : J, (admissibleGluingInclusion f B.I.blowupMap (W j)) ''
            ((admissibleGluingComparison f B.I.blowupMap (W j) (bj j) (c j) (hc j)) ⁻¹'
              (Vj j : Set ↥(Limits.pullback (f ∣_ W j) (bj j) : Scheme.{u}))) ∧
        Surjective (V.ι ≫ pullback.snd f B.I.blowupMap) ∧
        SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          ((@moduleStrictTransform X S f B.I
            (B.I.isFiniteType_toModules_sheaf B.finiteType) F inferInstance).restrict V.ι) := by
  sorry

end Scheme.Modules

end AlgebraicGeometry
