/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.CategoryTheory.Sites.Point.Over

/-! A finite locally constant set sheaf has finitely generated geometric stalks.

This is the intermediate finiteness assertion used to obtain finite stalks.
(blueprint: lem-galois-flc-set-is-finite-sheaf)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

-- The sheafification map and π are locally surjective. A common pointed refinement
-- puts any germ over U, and the lifted image sieve supplies its constant representative.
private theorem germ_constant_epi_surjective {Y : Scheme.{u}}
    (G : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (U : Y.Etale) (a : (pointSmallEtale y).fiber.obj U) (M : Type (u + 1))
    (π : (constantSheaf (Y.smallEtaleTopology.over U) (Type (u + 1))).obj M ⟶
      G.over U) [Epi π] :
    Function.Surjective
      (((toSheafify (Y.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)).app
        (Opposite.op (Over.mk (𝟙 U)))) ≫ π.hom.app (Opposite.op (Over.mk (𝟙 U))) ≫
          (pointSmallEtale y).toPresheafFiber U a G.obj) := by
  classical
  let Φ := pointSmallEtale y
  let ψ := Φ.over a
  let η := toSheafify (Y.smallEtaleTopology.over U) ((Functor.const (Over U)ᵒᵖ).obj M)
  have : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi π).2 inferInstance
  have : Presheaf.IsLocallySurjective (Y.smallEtaleTopology.over U) π.hom := inferInstance
  have : Presheaf.IsLocallySurjective (Y.smallEtaleTopology.over U) (η ≫ π.hom) :=
    inferInstance
  intro z
  obtain ⟨V, b, t, ht⟩ := Φ.toPresheafFiber_jointly_surjective (P := G.obj) z
  obtain ⟨W, f, g, _⟩ := IsCofilteredOrEmpty.cone_objs
    (Functor.elementsMk Φ.fiber V b) (Functor.elementsMk Φ.fiber U a)
  let T : Over U := Over.mk g.1
  let c : ψ.fiber.obj T := ⟨W.2, by
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
    exact g.2⟩
  let t' : (G.over U).obj.obj (Opposite.op T) := G.obj.map f.1.op t
  obtain ⟨R, r, ⟨m, hm⟩, d, hd⟩ := ψ.jointly_surjective
    (Presheaf.imageSieve (η ≫ π.hom) t')
    (Presheaf.imageSieve_mem (Y.smallEtaleTopology.over U) (η ≫ π.hom) t') c
  refine ⟨m, ?_⟩
  have hda : Φ.fiber.map R.hom d.1 = a := by
    exact (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 d.2
  have hdr : Φ.fiber.map r.left d.1 = W.2 := congr_arg Subtype.val hd
  have hn := NatTrans.naturality_apply (η ≫ π.hom)
    (Over.homMk R.hom : R ⟶ Over.mk (𝟙 U)).op m
  dsimp at hn
  change Φ.toPresheafFiber U a G.obj ((η ≫ π.hom).app (Opposite.op (Over.mk (𝟙 U))) m) = z
  calc
    _ = Φ.toPresheafFiber R.left d.1 G.obj
        (G.obj.map R.hom.op ((η ≫ π.hom).app (Opposite.op (Over.mk (𝟙 U))) m)) := by
      exact (congr_arg (fun e ↦ Φ.toPresheafFiber U e G.obj
        ((η ≫ π.hom).app (Opposite.op (Over.mk (𝟙 U))) m)) hda).symm.trans
          (ConcreteCategory.congr_hom (Φ.toPresheafFiber_w R.hom d.1 G.obj) _).symm
    _ = Φ.toPresheafFiber R.left d.1 G.obj ((η ≫ π.hom).app (Opposite.op R) m) := by
      exact congr_arg (Φ.toPresheafFiber R.left d.1 G.obj) hn.symm
    _ = Φ.toPresheafFiber R.left d.1 G.obj (G.obj.map r.left.op t') := by
      exact congr_arg (Φ.toPresheafFiber R.left d.1 G.obj) hm
    _ = Φ.toPresheafFiber W.1 W.2 G.obj t' := by
      exact (ConcreteCategory.congr_hom
        (Φ.toPresheafFiber_w r.left d.1 G.obj) t').trans
          (congr_arg (fun e ↦ Φ.toPresheafFiber W.1 e G.obj t') hdr)
    _ = Φ.toPresheafFiber V b G.obj t := by
      exact (ConcreteCategory.congr_hom
        (Φ.toPresheafFiber_w f.1 W.2 G.obj) t).trans
          (congr_arg (fun e ↦ Φ.toPresheafFiber V e G.obj t) f.2)
    _ = z := ht

/-- (blueprint: lem-galois-flc-set-is-finite-sheaf) The finite locally constant
trivializations imply `IsFiniteSheaf`.

The proof follows the Stacks Project's reindexing argument for geometric stalks:
lift a geometric point to a member of the etale cover, identify the restricted
stalk with the stalk of the finite constant model, and use the constant
presheaf's terminal pointed neighbourhood. The proof reindexes pointed etale neighbourhoods
along a fibre product after lifting each
geometric point to a cover member. The resulting surjection from the restricted stalk, the
local constant-sheaf isomorphism, and the finite constant value show that every stalk is
finitely generated, which is exactly `IsFiniteSheaf` for types. -/
theorem isFiniteSheaf_of_finite_locally_constant_sets {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
      ∀ i, ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((F.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S)) : IsFiniteSheaf F := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨𝒰, h𝒰⟩ := hF
  constructor
  intro Ω _ _ s
  obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
  obtain ⟨S, hS, ⟨e⟩⟩ := h𝒰 i
  have : Finite S := hS
  let a : (pointSmallEtale s).fiber.obj (𝒰.etalePrecoverageToEtale i) :=
    Over.homMk t ht
  have hsurj := germ_constant_epi_surjective F Ω s
    (𝒰.etalePrecoverageToEtale i) a S e.inv
  have : Finite ((pointSmallEtale s).sheafFiber.obj F) :=
    Finite.of_surjective (α := S) _ hsurj
  exact (ConcreteCategory.isFinitelyGenerated_iff_finite _).2 inferInstance

end AlgebraicGeometry.Scheme
