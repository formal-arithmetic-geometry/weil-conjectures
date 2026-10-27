module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Representation by a prescribed open subscheme

Source: Stacks Project, Spaces Descent, Tag 041X, final two paragraphs of the proof of
`lemma-descending-property-open-immersion`, in its big-fppf-sheaf formulation
(blueprint: lem-trf-prescribed-open-fppf-sheaf-representation).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- An fppf sheaf represented étale-locally by the pullbacks of a specified open is uniquely
represented by that open, with the prescribed local identifications and the stated section formula.
Source: Stacks Project, Spaces Descent, Tag 041X, proof of
`lemma-descending-property-open-immersion`, final two paragraphs
(blueprint: lem-trf-prescribed-open-fppf-sheaf-representation).

Proof: (1) Étale morphisms are flat and locally finitely presented, so joint surjectivity makes
this an fppf covering. Base change gives fppf coverings of every test scheme, including the open.
(2) Maps into the open over the base are unique because an open immersion is a monomorphism.
The local representing isomorphisms therefore make sections on overlaps unique. The sections
obtained from the identities of the local opens agree and glue by the sheaf equalizer to b on U.
(3) Pulling b back along each map to U defines a natural transformation. Naturality of each local
isomorphism and the defining restrictions of b show that its local restrictions are prescribed.
(4) Given any section x on Z, the local isomorphisms give maps from the covering Z_i into U_i.
Joint surjectivity forces the image of Z in T to lie in U. The open-immersion factorization
criterion gives a unique map Z to U, without a reducedness assumption.
(5) The pullback of b along this map agrees with x on the covering, hence equals x by separatedness.
The components are bijective and their inverses are natural. This also gives the singleton/empty
alternative. (6) Any other isomorphism with the prescribed restrictions gives the same section b
by separatedness on U, and naturality then identifies all its components. Empty index sets and
empty opens are covered by the empty-cover sheaf axiom. -/
theorem existsUnique_prescribedOpen_fppfSheaf_representation
    (T : Scheme.{u}) (F : Sheaf (fppfTopology.over T) (Type (max u v)))
    (I : Type w) (Tᵢ : I → Scheme.{u}) (q : ∀ i, Tᵢ i ⟶ T)
    [∀ i, Etale (q i)] (hq : ∀ t : T, ∃ i, ∃ s : Tᵢ i, q i s = t)
    (U : T.Opens)
    (αᵢ : ∀ i,
      yoneda.obj (Over.mk (pullback.snd U.ι (q i))) ⋙ uliftFunctor.{v} ≅
        (Over.map (q i)).op ⋙ F.obj) :
    ∃ α : yoneda.obj (Over.mk U.ι) ⋙ uliftFunctor.{v} ≅ F.obj,
      (∀ (i : I) (W : Over (Tᵢ i)) (a : W ⟶ Over.mk (pullback.snd U.ι (q i))),
        α.hom.app (op ((Over.map (q i)).obj W))
            ⟨(Over.map (q i)).map a ≫
              Over.homMk (pullback.fst U.ι (q i)) pullback.condition⟩ =
          (αᵢ i).hom.app (op W) ⟨a⟩) ∧
      (∀ β : yoneda.obj (Over.mk U.ι) ⋙ uliftFunctor.{v} ≅ F.obj,
        (∀ (i : I) (W : Over (Tᵢ i)) (a : W ⟶ Over.mk (pullback.snd U.ι (q i))),
          β.hom.app (op ((Over.map (q i)).obj W))
              ⟨(Over.map (q i)).map a ≫
                Over.homMk (pullback.fst U.ι (q i)) pullback.condition⟩ =
            (αᵢ i).hom.app (op W) ⟨a⟩) → β = α) ∧
      (∀ (Z : Over T) (a : Z ⟶ Over.mk U.ι),
        α.hom.app (op Z) ⟨a⟩ =
          F.obj.map a.op (α.hom.app (op (Over.mk U.ι)) ⟨𝟙 (Over.mk U.ι)⟩)) ∧
      (∀ (Z : Over T) (x : F.obj.obj (op Z)),
        ∃! a : Z ⟶ Over.mk U.ι,
          x = F.obj.map a.op (α.hom.app (op (Over.mk U.ι)) ⟨𝟙 (Over.mk U.ι)⟩)) ∧
      (∀ Z : Over T,
        (Nonempty (Z ⟶ Over.mk U.ι) →
          Nonempty (F.obj.obj (op Z)) ∧ Subsingleton (F.obj.obj (op Z))) ∧
        (¬ Nonempty (Z ⟶ Over.mk U.ι) → IsEmpty (F.obj.obj (op Z)))) := by
  classical
  have hom_sub {S V : Scheme.{u}} (j : V ⟶ S) [Mono j] (Z : Over S) :
      Subsingleton (Z ⟶ Over.mk j) := by
    refine ⟨fun a b ↦ Over.OverMorphism.ext ?_⟩
    apply (cancel_mono j).1
    exact (Over.w a).trans (Over.w b).symm
  have hlocal (i : I) (W : Over (Tᵢ i)) :
      Subsingleton (F.obj.obj (op ((Over.map (q i)).obj W))) := by
    let := hom_sub (pullback.snd U.ι (q i)) W
    let : Subsingleton ((yoneda.obj (Over.mk (pullback.snd U.ι (q i))) ⋙
        uliftFunctor.{v}).obj (op W)) := by
      change Subsingleton (ULift.{v} (W ⟶ Over.mk (pullback.snd U.ι (q i))))
      infer_instance
    exact ((αᵢ i).app (op W)).toEquiv.symm.subsingleton
  have hlocal' (W : Over T) (i : I) (a : W.left ⟶ Tᵢ i)
      (ha : a ≫ q i = W.hom) : Subsingleton (F.obj.obj (op W)) := by
    let e : (Over.map (q i)).obj (Over.mk a) ≅ W :=
      Over.isoMk (Iso.refl W.left) (by simpa using ha.symm)
    let := hlocal i (Over.mk a)
    exact (F.obj.mapIso e.op).toEquiv.subsingleton
  let S : Sieve T := Sieve.ofArrows Tᵢ q
  have hS : S ∈ fppfTopology T := by
    apply Precoverage.generate_mem_toGrothendieck
    change Presieve.ofArrows Tᵢ q ∈ precoverage (@Flat ⊓ @LocallyOfFinitePresentation) T
    rw [ofArrows_mem_precoverage_iff]
    exact ⟨hq, fun i ↦ ⟨inferInstance, inferInstance⟩⟩
  let R (Z : Over T) : Sieve Z := (Sieve.overEquiv Z).symm (S.pullback Z.hom)
  have hR (Z : Over T) : R Z ∈ (fppfTopology.over T) Z :=
    fppfTopology.overEquiv_symm_mem_over Z _ (fppfTopology.pullback_stable Z.hom hS)
  have hfactor {Z W : Over T} (f : W ⟶ Z) (hf : R Z f) :
      ∃ (i : I) (a : W.left ⟶ Tᵢ i), a ≫ q i = W.hom := by
    obtain ⟨i, a, ha⟩ := (Sieve.mem_ofArrows_iff Tᵢ q _).1 hf
    exact ⟨i, a, ha.symm.trans (Over.w f)⟩
  have hsub (Z : Over T) : Subsingleton (F.obj.obj (op Z)) := by
    refine ⟨fun x y ↦ (F.property.isSheafFor (R Z) (hR Z)).isSeparatedFor.ext ?_⟩
    intro W f hf
    obtain ⟨i, a, ha⟩ := hfactor f hf
    let := hlocal' W i a ha
    exact Subsingleton.elim _ _
  let (Z : Over T) : Subsingleton (F.obj.obj (op Z)) := hsub Z
  have hb : Nonempty (F.obj.obj (op (Over.mk U.ι))) := by
    have hx (W : Over T) (f : W ⟶ Over.mk U.ι) (hf : R (Over.mk U.ι) f) :
        Nonempty (F.obj.obj (op W)) := by
      obtain ⟨i, a, ha⟩ := hfactor f hf
      let e : (Over.map (q i)).obj (Over.mk a) ≅ W :=
        Over.isoMk (Iso.refl W.left) (by simpa using ha.symm)
      let b : Over.mk a ⟶ Over.mk (pullback.snd U.ι (q i)) :=
        Over.homMk (pullback.lift f.left a ((Over.w f).trans ha.symm))
          (by simp)
      exact ⟨F.obj.map e.inv.op ((αᵢ i).hom.app (op (Over.mk a)) ⟨b⟩)⟩
    let x : Presieve.FamilyOfElements F.obj (R (Over.mk U.ι)).arrows :=
      fun W f hf ↦ (hx W f hf).some
    have hxcomp : x.Compatible := by
      intro W₁ W₂ W f₁ f₂ g₁ g₂ hg₁ hg₂ heq
      exact Subsingleton.elim _ _
    exact ⟨(F.property.isSheafFor (R (Over.mk U.ι)) (hR _)).amalgamate x hxcomp⟩
  obtain ⟨b⟩ := hb
  have hsupport (Z : Over T) (x : F.obj.obj (op Z)) : Nonempty (Z ⟶ Over.mk U.ι) := by
    have himage : Set.range Z.hom ⊆ Set.range U.ι := by
      rintro _ ⟨z, rfl⟩
      obtain ⟨i, t, ht⟩ := hq (Z.hom z)
      obtain ⟨p, hp, _⟩ := Pullback.exists_preimage_pullback
        (f := Z.hom) (g := q i) z t ht.symm
      let W : Over (Tᵢ i) := Over.mk (pullback.snd Z.hom (q i))
      let pZ : (Over.map (q i)).obj W ⟶ Z :=
        Over.homMk (pullback.fst Z.hom (q i)) pullback.condition
      let a : W ⟶ Over.mk (pullback.snd U.ι (q i)) :=
        ((αᵢ i).inv.app (op W) (F.obj.map pZ.op x)).down
      have heq : (a.left ≫ pullback.fst U.ι (q i)) ≫ U.ι =
          pullback.fst Z.hom (q i) ≫ Z.hom := by
        rw [Category.assoc, pullback.condition, ← Category.assoc]
        exact (congrArg (fun f ↦ f ≫ q i) (Over.w a)).trans pullback.condition.symm
      refine ⟨(a.left ≫ pullback.fst U.ι (q i)) p, ?_⟩
      rw [← Scheme.Hom.comp_apply, heq, Scheme.Hom.comp_apply]
      exact congrArg Z.hom hp
    exact ⟨Over.homMk (IsOpenImmersion.lift U.ι Z.hom himage)
      (IsOpenImmersion.lift_fac _ _ _)⟩
  let η : yoneda.obj (Over.mk U.ι) ⋙ uliftFunctor.{v} ⟶ F.obj :=
    uliftYonedaEquiv.symm b
  have hbij (Z : (Over T)ᵒᵖ) : Function.Bijective (η.app Z) := by
    let := hom_sub U.ι Z.unop
    let : Subsingleton ((yoneda.obj (Over.mk U.ι) ⋙ uliftFunctor.{v}).obj Z) := by
      change Subsingleton (ULift.{v} (Z.unop ⟶ Over.mk U.ι))
      infer_instance
    refine ⟨Function.injective_of_subsingleton _, fun x ↦ ?_⟩
    obtain ⟨a⟩ := hsupport Z.unop x
    exact ⟨⟨a⟩, Subsingleton.elim _ _⟩
  let (Z : (Over T)ᵒᵖ) : IsIso (η.app Z) :=
    (isIso_iff_bijective _).2 (hbij Z)
  let : IsIso η := NatIso.isIso_of_isIso_app η
  let α : yoneda.obj (Over.mk U.ι) ⋙ uliftFunctor.{v} ≅ F.obj := asIso η
  refine ⟨α, ?_, ?_, ?_, ?_, ?_⟩
  · intro i W a
    exact Subsingleton.elim _ _
  · intro β _
    apply Iso.ext
    ext Z a
    exact Subsingleton.elim _ _
  · intro Z a
    exact Subsingleton.elim _ _
  · intro Z x
    obtain ⟨a⟩ := hsupport Z x
    let := hom_sub U.ι Z
    exact ⟨a, Subsingleton.elim _ _, fun a' _ ↦ Subsingleton.elim _ _⟩
  · intro Z
    refine ⟨?_, ?_⟩
    · rintro ⟨a⟩
      exact ⟨⟨F.obj.map a.op b⟩, inferInstance⟩
    · intro h
      exact ⟨fun x ↦ h (hsupport Z x)⟩

end AlgebraicGeometry.Scheme
