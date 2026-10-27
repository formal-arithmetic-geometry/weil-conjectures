module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Grothendieck transfer and exact integer orbit sums

Source: Stacks Project, Tag 079B and the proof of `lemma-F-G-monos` in `injectives.tex`;
`WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean`, `isGrothendieckAbelian`;
`DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean`, `Free.preservesHomology_functor`
(blueprint: lem-sf-created-grothendieck-exact-integer-sum).

The finite-subsum diagram, its cocone, its natural comparison, and the kernel/cokernel
comparisons are Mathlib's canonical constructions. No choices of arbitrary comparison maps
are part of the statement. In an abelian category `IsSeparator G` is the generator convention
of Tag 079B: every proper subobject is missed by a map from `G`. Indeed, a separator detects
the nonzero cokernel of a proper mono; conversely this property applied to the kernel of a
nonzero difference of arrows detects that difference.
-/

@[expose] public section

set_option autoImplicit false

universe w v₁ v₂ u₁ u₂

open CategoryTheory Limits CoproductsFromFiniteFiltered

namespace CategoryTheory

/-- Grothendieck transfer, exact coproducts with their canonical finite-subsum presentation,
and exactness of an additive left adjoint whose underlying functor is an integer orbit sum.
Source: Stacks Project, Tag 079B, its following discussion and `lemma-F-G-monos`;
`Endofunctor/IsoAlgebra.lean`, `isGrothendieckAbelian`, and
`DerivedCategory/RightDerivedFunctor/IsoAlgebra.lean`, `Free.preservesHomology_functor`
(blueprint: lem-sf-created-grothendieck-exact-integer-sum).

Proof (the node's nine steps):
1. Creation lifts every small colimit in `C` to `D`, and makes `U` preserve its cocone and maps.
2. For a proper mono `i`, exactness makes `U.map i` monic and conservativity makes it proper.
A map from `G` missing it transposes under `adj` to a map from `L.obj G` missing `i`, by
naturality of the adjunction's hom equivalence. This transfers the generator.
3. Apply the singleton case of `JointlyReflectIsomorphisms.shortExact_iff` to `U`. AB5 in `C`
and the colimit identifications of step 1 give exact filtered colimits in `D`. Together with
step 2 and local smallness these give `IsGrothendieckAbelian.{w} D`.
4. Finite subsets, including the empty subset, form a small filtered poset. The transition
maps on finite coproducts include each old summand into the same summand. A cocone is
uniquely specified by its singleton legs, so the canonical cocone on the full sum is colimiting.
5. For a map of families the finite-sum map sends each coprojection to the corresponding
coprojection after the given component map. Passing to the colimit gives the same formula
for the full sum. This proves the displayed naturality square for `liftToFinsetColimIso`.
6. Finite biproducts preserve kernels and cokernels componentwise: factor a kernel lift on
each projection, or a cokernel descent on each inclusion, and use the biproduct universal
property. The empty sum is the zero object. This gives exactness of finite subsum sequences
and of the functor `liftToFinset`.
7. `HasExactColimitsOfShape.preservesFiniteLimits` for the filtered finite-subset category
makes the kernel comparison invertible. AB5 makes the filtered colimit of the finite short
exact sequences short exact. Steps 4-5 identify both arrows with the coproduct arrows.
8. Cokernels commute with colimits by their universal property. Thus the canonical kernel
and cokernel comparisons below identify the finite sums, their filtered colimits, and the
full sum, including the kernel inclusions and quotient maps. For a commuting square,
naturality follows by cancelling the monic kernel inclusion or epic cokernel quotient.
9. Apply these results to the family `P n` acting on a short exact sequence. Each term is
short exact by the assumed exactness of `P n`; step 7 makes their sum short exact. The natural
isomorphism `e` identifies it with `L ⋙ U` on objects and arrows. Reflect short exactness
through `U`. The kernel and cokernel comparisons for `L` become invertible after `U` and
hence are invertible by conservativity. Additivity then supplies all finite limits and
colimits, since equalizers and coequalizers are kernels and cokernels of differences. -/
theorem createdGrothendieck_exactIntegerSum
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [LocallySmall.{w} D]
    (U : D ⥤ C) [U.Additive] [U.Faithful] [U.ReflectsIsomorphisms]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U] [CreatesColimitsOfSize.{w, w} U]
    (L : C ⥤ D) [L.Additive] (adj : L ⊣ U) :
    (∀ G : C, IsSeparator G → IsSeparator (L.obj G)) ∧
    IsGrothendieckAbelian.{w} D ∧
    (∀ I : Type w,
      exactFunctor (Discrete I ⥤ C) C colim ∧
      (∀ S : ShortComplex (Discrete I ⥤ C),
        (∀ i : Discrete I, (S.map ((evaluation (Discrete I) C).obj i)).ShortExact) →
          (S.map colim).ShortExact) ∧
      (∀ X : I → C,
        Nonempty (IsColimit (finiteSubcoproductsCocone X)) ∧
        IsIso (colimit.desc (liftToFinsetObj (Discrete.functor X))
          (finiteSubcoproductsCocone X))) ∧
      (∀ (F G : Discrete I ⥤ C) (a : F ⟶ G),
        colim.map ((liftToFinset C I).map a) ≫ liftToFinsetColimIso.hom.app G =
          liftToFinsetColimIso.hom.app F ≫ colim.map a) ∧
      exactFunctor (Discrete I ⥤ C) (Finset (Discrete I) ⥤ C) (liftToFinset C I) ∧
      (∀ (J : Finset (Discrete I)) (F G : Discrete J ⥤ C) (a : F ⟶ G),
        IsIso (kernelComparison a (colim (J := Discrete J) (C := C))) ∧
        IsIso (cokernelComparison a (colim (J := Discrete J) (C := C)))) ∧
      (∀ (F G : Discrete I ⥤ C) (a : F ⟶ G),
        IsIso (kernelComparison ((liftToFinset C I).map a)
          (colim (J := Finset (Discrete I)) (C := C))) ∧
        IsIso (cokernelComparison ((liftToFinset C I).map a)
          (colim (J := Finset (Discrete I)) (C := C))) ∧
        IsIso (kernelComparison a (colim (J := Discrete I) (C := C))) ∧
        IsIso (cokernelComparison a (colim (J := Discrete I) (C := C))))) ∧
    (∀ (P : ℤ → C ⥤ C) [∀ n : ℤ, (P n).Additive] [∀ n : ℤ, (P n).IsEquivalence],
      (∀ n : ℤ, exactFunctor C C (P n)) →
      (L ⋙ U ≅ ∐ P) →
      exactFunctor C C (L ⋙ U) ∧ exactFunctor C D L ∧
      ∀ S : ShortComplex C, S.ShortExact →
        (S.map (L ⋙ U)).ShortExact ∧ (S.map L).ShortExact) := by
  classical
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  have hsep : ∀ G : C, IsSeparator G → IsSeparator (L.obj G) := by
    intro G hG
    rw [isSeparator_def] at hG ⊢
    intro X Y f g hfg
    apply U.map_injective
    apply hG
    intro a
    have h := congrArg (adj.homEquiv G Y) (hfg ((adj.homEquiv G X).symm a))
    simpa only [adj.homEquiv_naturality_right, Equiv.apply_symm_apply] using h
  have : HasColimitsOfSize.{w, w} D :=
    hasColimits_of_hasColimits_createsColimits U
  have : HasFilteredColimitsOfSize.{w, w} D := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{w, w} D :=
    ⟨fun J _ _ ↦ HasExactColimitsOfShape.domain_of_functor J U⟩
  obtain ⟨G, hG⟩ := HasSeparator.hasSeparator (C := C)
  have : HasSeparator D := ⟨L.obj G, hsep G hG⟩
  refine ⟨hsep, {}, ?_, ?_⟩
  · intro I
    have : PreservesFiniteColimits (liftToFinset C I) :=
      preservesFiniteColimits_of_evaluation _ fun J ↦ by
        have : PreservesFiniteColimits
            ((Functor.whiskeringLeft (Discrete J) (Discrete I) C).obj
              (Discrete.functor (·.val))) := ⟨fun _ _ _ ↦ inferInstance⟩
        exact preservesFiniteColimits_of_natIso (liftToFinsetEvaluationIso J).symm
    refine ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro S hS
      have hEval : JointlyReflectIsomorphisms
          (fun i : Discrete I ↦ (evaluation (Discrete I) C).obj i) :=
        ⟨fun f h ↦ by
          have : ∀ i, IsIso (f.app i) := fun i ↦ h i
          exact NatIso.isIso_of_isIso_app f⟩
      exact ((hEval.shortExact_iff S).2 hS).map_of_exact colim
    · intro X
      refine ⟨⟨isColimitFiniteSubproductsCocone X⟩, ?_⟩
      exact ((colimit.isColimit _).nonempty_isColimit_iff_isIso_desc).1
        ⟨isColimitFiniteSubproductsCocone X⟩
    · intro F G a
      exact liftToFinsetColimIso.hom.naturality a
    · exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
    · intro J F G a
      exact ⟨inferInstance, inferInstance⟩
    · intro F G a
      exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  · intro P _ _ hP e
    have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0} C
    let Q : Discrete ℤ ⥤ C ⥤ C := Discrete.functor P
    have hlim : ∀ n, PreservesFiniteLimits (P n) := fun n ↦ ((exactFunctor_iff _).1 (hP n)).1
    have hcolim : ∀ n, PreservesFiniteColimits (P n) :=
      fun n ↦ ((exactFunctor_iff _).1 (hP n)).2
    have : PreservesFiniteLimits Q.flip :=
      preservesFiniteLimits_of_evaluation _ fun n ↦ by
        change PreservesFiniteLimits (P n.as)
        infer_instance
    have : PreservesFiniteColimits Q.flip :=
      preservesFiniteColimits_of_evaluation _ fun n ↦ by
        change PreservesFiniteColimits (P n.as)
        infer_instance
    have : PreservesFiniteLimits (Q.flip ⋙ colim) := comp_preservesFiniteLimits _ _
    have : PreservesFiniteColimits (Q.flip ⋙ colim) := comp_preservesFiniteColimits _ _
    have : PreservesFiniteLimits (∐ P) :=
      preservesFiniteLimits_of_natIso (colimitIsoFlipCompColim Q).symm
    have : PreservesFiniteColimits (∐ P) :=
      preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim Q).symm
    have : PreservesFiniteLimits (L ⋙ U) := preservesFiniteLimits_of_natIso e.symm
    have : PreservesFiniteColimits (L ⋙ U) := preservesFiniteColimits_of_natIso e.symm
    have : PreservesFiniteLimits L := preservesFiniteLimits_of_reflects_of_preserves L U
    have : PreservesFiniteColimits L := preservesFiniteColimits_of_reflects_of_preserves L U
    exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      fun S hS ↦ ⟨hS.map_of_exact _, hS.map_of_exact _⟩⟩

end CategoryTheory
