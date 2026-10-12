module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Mathlib.Order.Bounds.OrderIso

/-!
# Page induction for morphisms of spectral sequences

Source: blueprint `lem-sp-page-induction` (blueprint: lem-sp-page-induction).

Spectral sequences are Mathlib's `SpectralSequence` (node `def-sp-spectral-sequence`) on
bidegrees `ℤ × ℤ`, starting at page `2`. The limiting page is formed as in
`def-sp-convergence` (`CategoryTheory.BigradedExactCouple.CycleBoundaryTower`,
`LimitSubobjects`, `pageInfinity`), with the recursion applied to the pages and differentials
of the spectral sequence: cycles `Z r p q` and boundaries `B r p q` are subobjects of
`E_2^{p,q}`, `Z 2 = ⊤`, `B 2 = ⊥`, the projection `π 2` is the inclusion, `Z (r+1)` and
`B (r+1)` are the images in `E_2` of the inverse images of `ker d_r` and `im d_r` under
`π r : Z_r → E_r`, and `π (r+1)` is the lift of `π r` to the cycles of `E_r` followed by the
homology projection and the structure isomorphism `H(E_r) ≅ E_{r+1}`. `E_∞ = Z_∞/B_∞` is the
cokernel of `Z_∞ ∩ B_∞ ⊆ Z_∞` (which is `B_∞ ⊆ Z_∞`), for a greatest lower bound `Z_∞` of the
`Z_r` and a least upper bound `B_∞` of the `B_r`, when these exist.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

private theorem subobject_quotient_iso
    {C : Type u} [Category.{v} C] [Abelian C] {X Y : C} (f : X ⟶ Y) [IsIso f]
    (Z B : Subobject X) (Z' B' : Subobject Y)
    (hZ : (Subobject.map f).obj Z = Z') (hB : (Subobject.map f).obj B = B') :
    ∃ (u : (Z : C) ⟶ (Z' : C))
      (ψ : cokernel ((Subobject.pullback Z.arrow).obj B).arrow ⟶
        cokernel ((Subobject.pullback Z'.arrow).obj B').arrow),
      u ≫ Z'.arrow = Z.arrow ≫ f ∧
      cokernel.π _ ≫ ψ = u ≫ cokernel.π _ ∧ IsIso ψ := by
  have hz : Subobject.mk (Z.arrow ≫ f) = Subobject.mk Z'.arrow := by
    simpa only [← Subobject.map_mk, Subobject.mk_arrow] using hZ
  let z := Subobject.isoOfMkEqMk (Z.arrow ≫ f) Z'.arrow hz
  have zcomm : z.hom ≫ Z'.arrow = Z.arrow ≫ f := by simp [z]
  let P := (Subobject.pullback Z.arrow).obj B
  let P' := (Subobject.pullback Z'.arrow).obj B'
  have hp : (Subobject.map z.hom).obj P = P' := by
    dsimp [P, P']
    rw [Subobject.map_pullback zcomm.symm
      (IsPullback.of_vert_isIso ⟨zcomm.symm⟩).isLimit, hB]
  have hb : Subobject.mk (P.arrow ≫ z.hom) = Subobject.mk P'.arrow := by
    simpa only [← Subobject.map_mk, Subobject.mk_arrow] using hp
  let b := Subobject.isoOfMkEqMk (P.arrow ≫ z.hom) P'.arrow hb
  let e := cokernel.mapIso P.arrow P'.arrow b z (by simp [b])
  refine ⟨z.hom, e.hom, zcomm, ?_, inferInstance⟩
  change cokernel.π P.arrow ≫ e.hom = z.hom ≫ cokernel.π P'.arrow
  simp [e, cokernel.mapIso]

private theorem map_kernel_of_iso_square
    {C : Type u} [Category.{v} C] [Abelian C] {X Y X' Y' : C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ≅ X') (b : Y ≅ Y')
    (h : f ≫ b.hom = a.hom ≫ f') :
    (Subobject.map a.hom).obj (kernelSubobject f) = kernelSubobject f' := by
  rw [← kernelSubobject_comp_mono f b.hom]
  simp only [h]
  have he := Subobject.mk_eq_mk_of_comm
    ((kernelSubobject (a.hom ≫ f')).arrow ≫ a.hom) (kernelSubobject f').arrow
    (kernelSubobjectIsoComp a.hom f') (by simp)
  simpa only [← Subobject.map_mk, Subobject.mk_arrow] using he

private theorem map_image_of_iso_square
    {C : Type u} [Category.{v} C] [Abelian C] {X Y X' Y' : C}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ≅ X') (b : Y ≅ Y')
    (h : f ≫ b.hom = a.hom ≫ f') :
    (Subobject.map b.hom).obj (imageSubobject f) = imageSubobject f' := by
  have he := Subobject.mk_eq_mk_of_comm
    ((imageSubobject f).arrow ≫ b.hom) (imageSubobject (f ≫ b.hom)).arrow
    (imageSubobjectCompIso f b.hom).symm (by
      rw [← cancel_mono (inv b.hom)]
      simp)
  have ht : (Subobject.map b.hom).obj (imageSubobject f) =
      imageSubobject (f ≫ b.hom) := by
    simpa only [← Subobject.map_mk, Subobject.mk_arrow] using he
  rw [ht]
  simp only [h, imageSubobject_iso_comp]

/-- An isomorphism on every finite page transports the recursive cycle and boundary
subobjects of the second page.

Proof: Induct on the integer page index, starting at 2. Strengthen the inductive claim
by retaining an isomorphism between the cycle objects whose composite with the target
inclusion is the source inclusion followed by the second-page map, and whose composite
with the target projection is the source projection followed by the current page map.
At page 2, both cycle subobjects are top and both boundaries are bottom; the projection
identities give the strengthened compatibility. In the successor step, the page map is
an isomorphism of complexes. The chain-map equations therefore identify both the kernel
of the outgoing differential and the image of the incoming differential. The compatible
square of cycle projections, whose vertical arrows are isomorphisms, identifies their
pullbacks. Composing with the cycle inclusions gives exactly the two successor subobjects
in the hypotheses. Restrict the cycle isomorphism to the pulled-back kernels. Its induced
map on cycles commutes with their inclusions by the kernel universal property. Naturality
of the homology projection, followed by the spectral-sequence morphism's homology square,
proves compatibility with the successor projections. This supplies the strengthened
induction hypothesis for the next page.

Source: blueprint lem-sp-page-induction, Proof, finite-subobject induction in Step 3
(blueprint: lem-sp-page-induction). -/
private theorem spectralSequence_finite_subobject_transport
    {C : Type u} [Category.{v} C] [Abelian C]
    {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E E' : SpectralSequence C c 2) (φ : E ⟶ E')
    (h₂ : ∀ (p q : ℤ), IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩))
    -- the cycle/boundary recursion of `def-sp-convergence` for `E`
    (Z B : ∀ (_ : ℤ) (p q : ℤ), Subobject ((E.page 2 le_rfl).X ⟨p, q⟩))
    (π : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z r p q : C) ⟶ (E.page r hr).X ⟨p, q⟩)
    (hZ₂ : ∀ p q : ℤ, Z 2 p q = ⊤) (hB₂ : ∀ p q : ℤ, B 2 p q = ⊥)
    (hπ₂ : ∀ p q : ℤ, π 2 le_rfl p q = (Z 2 p q).arrow)
    (hZ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), Z (r + 1) p q =
      (Subobject.«exists» (Z r p q).arrow).obj
        ((Subobject.pullback (π r hr p q)).obj (kernelSubobject ((E.page r hr).dFrom ⟨p, q⟩))))
    (hB : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), B (r + 1) p q =
      (Subobject.«exists» (Z r p q).arrow).obj
        ((Subobject.pullback (π r hr p q)).obj (imageSubobject ((E.page r hr).dTo ⟨p, q⟩))))
    (ι : ∀ (r : ℤ) (_hr : 2 ≤ r) (p q : ℤ), (Z (r + 1) p q : C) ⟶ (Z r p q : C))
    (hι : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ι r hr p q ≫ (Z r p q).arrow = (Z (r + 1) p q).arrow)
    (κ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z (r + 1) p q : C) ⟶ (E.page r hr).cycles ⟨p, q⟩)
    (hκ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      κ r hr p q ≫ (E.page r hr).iCycles ⟨p, q⟩ = ι r hr p q ≫ π r hr p q)
    (hπ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), π (r + 1) (by omega) p q =
      κ r hr p q ≫ (E.page r hr).homologyπ ⟨p, q⟩ ≫ (E.iso r (r + 1) ⟨p, q⟩ rfl hr).hom)
    -- the same recursion for `E'`
    (Z' B' : ∀ (_ : ℤ) (p q : ℤ), Subobject ((E'.page 2 le_rfl).X ⟨p, q⟩))
    (π' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' r p q : C) ⟶ (E'.page r hr).X ⟨p, q⟩)
    (hZ₂' : ∀ p q : ℤ, Z' 2 p q = ⊤) (hB₂' : ∀ p q : ℤ, B' 2 p q = ⊥)
    (hπ₂' : ∀ p q : ℤ, π' 2 le_rfl p q = (Z' 2 p q).arrow)
    (hZ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), Z' (r + 1) p q =
      (Subobject.«exists» (Z' r p q).arrow).obj
        ((Subobject.pullback (π' r hr p q)).obj (kernelSubobject ((E'.page r hr).dFrom ⟨p, q⟩))))
    (hB' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), B' (r + 1) p q =
      (Subobject.«exists» (Z' r p q).arrow).obj
        ((Subobject.pullback (π' r hr p q)).obj (imageSubobject ((E'.page r hr).dTo ⟨p, q⟩))))
    (ι' : ∀ (r : ℤ) (_hr : 2 ≤ r) (p q : ℤ), (Z' (r + 1) p q : C) ⟶ (Z' r p q : C))
    (hι' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ι' r hr p q ≫ (Z' r p q).arrow = (Z' (r + 1) p q).arrow)
    (κ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' (r + 1) p q : C) ⟶ (E'.page r hr).cycles ⟨p, q⟩)
    (hκ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      κ' r hr p q ≫ (E'.page r hr).iCycles ⟨p, q⟩ = ι' r hr p q ≫ π' r hr p q)
    (hπ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), π' (r + 1) (by omega) p q =
      κ' r hr p q ≫ (E'.page r hr).homologyπ ⟨p, q⟩ ≫ (E'.iso r (r + 1) ⟨p, q⟩ rfl hr).hom)
    (hpages : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      IsIso ((φ.hom r hr).f ⟨p, q⟩)) :
    ∀ (r : ℤ), 2 ≤ r → ∀ p q : ℤ,
      (Subobject.«exists» ((φ.hom 2 le_rfl).f ⟨p, q⟩)).obj (Z r p q) = Z' r p q ∧
      (Subobject.«exists» ((φ.hom 2 le_rfl).f ⟨p, q⟩)).obj (B r p q) = B' r p q := by
  have hstrong : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ∃ z : (Z r p q : C) ≅ (Z' r p q : C),
        z.hom ≫ (Z' r p q).arrow = (Z r p q).arrow ≫ (φ.hom 2 le_rfl).f ⟨p, q⟩ ∧
        z.hom ≫ π' r hr p q = π r hr p q ≫ (φ.hom r hr).f ⟨p, q⟩ ∧
        (Subobject.«exists» ((φ.hom 2 le_rfl).f ⟨p, q⟩)).obj (B r p q) = B' r p q := by
    intro r
    refine Int.inductionOn' r 2 ?_ ?_ ?_
    · intro hr p q
      have : IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩) := h₂ p q
      have hz : (Subobject.map ((φ.hom 2 le_rfl).f ⟨p, q⟩)).obj (Z 2 p q) =
          Z' 2 p q := by
        rw [hZ₂, hZ₂']
        exact (Subobject.mapIsoToOrderIso (asIso ((φ.hom 2 le_rfl).f ⟨p, q⟩))).map_top
      have he : Subobject.mk ((Z 2 p q).arrow ≫ (φ.hom 2 le_rfl).f ⟨p, q⟩) =
          Subobject.mk (Z' 2 p q).arrow := by
        simpa only [← Subobject.map_mk, Subobject.mk_arrow] using hz
      let z := Subobject.isoOfMkEqMk _ _ he
      refine ⟨z, ?_, ?_, ?_⟩
      · simp [z]
      · rw [hπ₂, hπ₂']
        simp [z]
      · rw [hB₂, hB₂', Subobject.exists_iso_map]
        exact (Subobject.mapIsoToOrderIso (asIso ((φ.hom 2 le_rfl).f ⟨p, q⟩))).map_bot
    · intro r hr ih _ p q
      obtain ⟨z, hz, hproj, hb⟩ := ih hr p q
      have : ∀ pq : ℤ × ℤ, IsIso ((φ.hom r hr).f pq) := fun pq ↦ hpages r hr pq.1 pq.2
      have : IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩) := h₂ p q
      let a := asIso ((φ.hom r hr).f ⟨p, q⟩)
      have hk := map_kernel_of_iso_square ((E.page r hr).dFrom ⟨p, q⟩)
        ((E'.page r hr).dFrom ⟨p, q⟩) a (asIso ((φ.hom r hr).next ⟨p, q⟩))
        ((φ.hom r hr).comm_from ⟨p, q⟩).symm
      have him := map_image_of_iso_square ((E.page r hr).dTo ⟨p, q⟩)
        ((E'.page r hr).dTo ⟨p, q⟩) (asIso ((φ.hom r hr).prev ⟨p, q⟩)) a
        ((φ.hom r hr).comm_to ⟨p, q⟩).symm
      change (Subobject.map ((φ.hom r hr).f ⟨p, q⟩)).obj _ = _ at hk
      change (Subobject.map ((φ.hom r hr).f ⟨p, q⟩)).obj _ = _ at him
      have hker : (Subobject.map z.hom).obj
          ((Subobject.pullback (π r hr p q)).obj
            (kernelSubobject ((E.page r hr).dFrom ⟨p, q⟩))) =
          (Subobject.pullback (π' r hr p q)).obj
            (kernelSubobject ((E'.page r hr).dFrom ⟨p, q⟩)) := by
        rw [Subobject.map_pullback hproj.symm
          (IsPullback.of_vert_isIso ⟨hproj.symm⟩).isLimit, hk]
      have himg : (Subobject.map z.hom).obj
          ((Subobject.pullback (π r hr p q)).obj
            (imageSubobject ((E.page r hr).dTo ⟨p, q⟩))) =
          (Subobject.pullback (π' r hr p q)).obj
            (imageSubobject ((E'.page r hr).dTo ⟨p, q⟩)) := by
        rw [Subobject.map_pullback hproj.symm
          (IsPullback.of_vert_isIso ⟨hproj.symm⟩).isLimit, him]
      have hzn : (Subobject.map ((φ.hom 2 le_rfl).f ⟨p, q⟩)).obj
          (Z (r + 1) p q) = Z' (r + 1) p q := by
        rw [hZ r hr p q, hZ' r hr p q, Subobject.exists_iso_map,
          Subobject.exists_iso_map, ← Subobject.map_comp]
        simp only [← hz, Subobject.map_comp, hker]
      have hbn : (Subobject.«exists» ((φ.hom 2 le_rfl).f ⟨p, q⟩)).obj
          (B (r + 1) p q) = B' (r + 1) p q := by
        rw [Subobject.exists_iso_map, hB r hr p q, hB' r hr p q,
          Subobject.exists_iso_map, Subobject.exists_iso_map,
          ← Subobject.map_comp]
        simp only [← hz, Subobject.map_comp, himg]
      have hen : Subobject.mk ((Z (r + 1) p q).arrow ≫ (φ.hom 2 le_rfl).f ⟨p, q⟩) =
          Subobject.mk (Z' (r + 1) p q).arrow := by
        simpa only [← Subobject.map_mk, Subobject.mk_arrow] using hzn
      let zn := Subobject.isoOfMkEqMk _ _ hen
      have hzncomm : zn.hom ≫ (Z' (r + 1) p q).arrow =
          (Z (r + 1) p q).arrow ≫ (φ.hom 2 le_rfl).f ⟨p, q⟩ := by simp [zn]
      have hinc : zn.hom ≫ ι' r hr p q = ι r hr p q ≫ z.hom := by
        apply (cancel_mono (Z' r p q).arrow).mp
        rw [Category.assoc, hι', hzncomm, Category.assoc, hz, ← Category.assoc, hι]
      have hcyc : zn.hom ≫ κ' r hr p q =
          κ r hr p q ≫ HomologicalComplex.cyclesMap (φ.hom r hr) ⟨p, q⟩ := by
        apply (cancel_mono ((E'.page r hr).iCycles ⟨p, q⟩)).mp
        simp only [Category.assoc, hκ', HomologicalComplex.cyclesMap_i]
        rw [← Category.assoc zn.hom (ι' r hr p q), hinc, Category.assoc, hproj,
          ← Category.assoc (ι r hr p q), ← hκ r hr p q, Category.assoc]
      refine ⟨zn, hzncomm, ?_, hbn⟩
      rw [hπ r hr p q, hπ' r hr p q]
      rw [← Category.assoc zn.hom (κ' r hr p q), hcyc]
      simp only [Category.assoc]
      rw [← HomologicalComplex.homologyπ_naturality_assoc]
      rw [φ.comm r (r + 1) ⟨p, q⟩ rfl hr]
    · intro r hr _ hr' p q
      omega
  intro r hr p q
  obtain ⟨z, hz, _, hb⟩ := hstrong r hr p q
  have : IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩) := h₂ p q
  refine ⟨?_, hb⟩
  rw [Subobject.exists_iso_map, ← Subobject.mk_arrow (Z r p q), Subobject.map_mk]
  exact Subobject.mk_eq_of_comm _ z hz

set_option linter.unusedVariables false in
/-- Page induction (blueprint: lem-sp-page-induction). If a morphism `φ : E ⟶ E'` of
spectral sequences is an isomorphism on `E_2` in every bidegree, then it is an isomorphism on
every page `E_r`, `2 ≤ r`; and if the limiting cycles and boundaries of `E` and `E'` exist,
`φ_2` restricts to `u : Z_∞ → Z'_∞` and induces an isomorphism `ψ : E_∞ ≅ E'_∞`.

Proof: (1) By `def-sp-spectral-sequence`, each `φ_r` is a chain map and `φ_{r+1}` is the map
induced on homology under the identifications `H(E_r) ≅ E_{r+1}`. (2) `φ_2` is an isomorphism;
if `φ_r` is one, its commutation with `d_r` identifies kernels and images of the differentials,
so it induces an isomorphism on homology, and `φ_{r+1}` is an isomorphism; induct on `r`.
(3) By induction on `r`, the isomorphism `φ_2` maps `Z_r` onto `Z'_r` and `B_r` onto `B'_r`
and the induced map on `Z_r/B_r` is `φ_r`: for `r = 2` this is clear, and in the step
`φ_r` maps `ker d_r`, `im d_r` onto `ker d'_r`, `im d'_r`, so `φ_2` maps their inverse images
`Z_{r+1}`, `B_{r+1}` onto `Z'_{r+1}`, `B'_{r+1}`, inducing `φ_{r+1}` by (1). An isomorphism
carries greatest lower bounds and least upper bounds of subobjects to those of the images, so
`φ_2(Z_∞) = Z'_∞`, `φ_2(B_∞) = B'_∞`, and `φ_2` induces `E_∞ = Z_∞/B_∞ ≅ Z'_∞/B'_∞ = E'_∞`. -/
theorem spectralSequence_page_induction
    {C : Type u} [Category.{v} C] [Abelian C]
    {c : ℤ → ComplexShape (ℤ × ℤ)}
    (E E' : SpectralSequence C c 2) (φ : E ⟶ E')
    (h₂ : ∀ (p q : ℤ), IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩))
    -- the cycle/boundary recursion of `def-sp-convergence` for `E`
    (Z B : ∀ (_ : ℤ) (p q : ℤ), Subobject ((E.page 2 le_rfl).X ⟨p, q⟩))
    (π : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z r p q : C) ⟶ (E.page r hr).X ⟨p, q⟩)
    (hZ₂ : ∀ p q : ℤ, Z 2 p q = ⊤) (hB₂ : ∀ p q : ℤ, B 2 p q = ⊥)
    (hπ₂ : ∀ p q : ℤ, π 2 le_rfl p q = (Z 2 p q).arrow)
    (hZ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), Z (r + 1) p q =
      (Subobject.«exists» (Z r p q).arrow).obj
        ((Subobject.pullback (π r hr p q)).obj (kernelSubobject ((E.page r hr).dFrom ⟨p, q⟩))))
    (hB : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), B (r + 1) p q =
      (Subobject.«exists» (Z r p q).arrow).obj
        ((Subobject.pullback (π r hr p q)).obj (imageSubobject ((E.page r hr).dTo ⟨p, q⟩))))
    (ι : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z (r + 1) p q : C) ⟶ (Z r p q : C))
    (hι : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ι r hr p q ≫ (Z r p q).arrow = (Z (r + 1) p q).arrow)
    (κ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z (r + 1) p q : C) ⟶ (E.page r hr).cycles ⟨p, q⟩)
    (hκ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      κ r hr p q ≫ (E.page r hr).iCycles ⟨p, q⟩ = ι r hr p q ≫ π r hr p q)
    (hπ : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), π (r + 1) (by omega) p q =
      κ r hr p q ≫ (E.page r hr).homologyπ ⟨p, q⟩ ≫ (E.iso r (r + 1) ⟨p, q⟩ rfl hr).hom)
    -- the same recursion for `E'`
    (Z' B' : ∀ (_ : ℤ) (p q : ℤ), Subobject ((E'.page 2 le_rfl).X ⟨p, q⟩))
    (π' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' r p q : C) ⟶ (E'.page r hr).X ⟨p, q⟩)
    (hZ₂' : ∀ p q : ℤ, Z' 2 p q = ⊤) (hB₂' : ∀ p q : ℤ, B' 2 p q = ⊥)
    (hπ₂' : ∀ p q : ℤ, π' 2 le_rfl p q = (Z' 2 p q).arrow)
    (hZ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), Z' (r + 1) p q =
      (Subobject.«exists» (Z' r p q).arrow).obj
        ((Subobject.pullback (π' r hr p q)).obj (kernelSubobject ((E'.page r hr).dFrom ⟨p, q⟩))))
    (hB' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), B' (r + 1) p q =
      (Subobject.«exists» (Z' r p q).arrow).obj
        ((Subobject.pullback (π' r hr p q)).obj (imageSubobject ((E'.page r hr).dTo ⟨p, q⟩))))
    (ι' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' (r + 1) p q : C) ⟶ (Z' r p q : C))
    (hι' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      ι' r hr p q ≫ (Z' r p q).arrow = (Z' (r + 1) p q).arrow)
    (κ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), (Z' (r + 1) p q : C) ⟶ (E'.page r hr).cycles ⟨p, q⟩)
    (hκ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      κ' r hr p q ≫ (E'.page r hr).iCycles ⟨p, q⟩ = ι' r hr p q ≫ π' r hr p q)
    (hπ' : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), π' (r + 1) (by omega) p q =
      κ' r hr p q ≫ (E'.page r hr).homologyπ ⟨p, q⟩ ≫ (E'.iso r (r + 1) ⟨p, q⟩ rfl hr).hom)
    -- existence of the limiting cycles and boundaries of `E` and `E'`
    (Zinf Binf : ∀ p q : ℤ, Subobject ((E.page 2 le_rfl).X ⟨p, q⟩))
    (hZinf : ∀ p q : ℤ, IsGLB {S | ∃ r : ℤ, 2 ≤ r ∧ S = Z r p q} (Zinf p q))
    (hBinf : ∀ p q : ℤ, IsLUB {S | ∃ r : ℤ, 2 ≤ r ∧ S = B r p q} (Binf p q))
    (Zinf' Binf' : ∀ p q : ℤ, Subobject ((E'.page 2 le_rfl).X ⟨p, q⟩))
    (hZinf' : ∀ p q : ℤ, IsGLB {S | ∃ r : ℤ, 2 ≤ r ∧ S = Z' r p q} (Zinf' p q))
    (hBinf' : ∀ p q : ℤ, IsLUB {S | ∃ r : ℤ, 2 ≤ r ∧ S = B' r p q} (Binf' p q)) :
    (∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), IsIso ((φ.hom r hr).f ⟨p, q⟩)) ∧
      ∀ p q : ℤ, ∃ (u : (Zinf p q : C) ⟶ (Zinf' p q : C))
        (ψ : cokernel ((Subobject.pullback (Zinf p q).arrow).obj (Binf p q)).arrow ⟶
          cokernel ((Subobject.pullback (Zinf' p q).arrow).obj (Binf' p q)).arrow),
        u ≫ (Zinf' p q).arrow = (Zinf p q).arrow ≫ (φ.hom 2 le_rfl).f ⟨p, q⟩ ∧
        cokernel.π _ ≫ ψ = u ≫ cokernel.π _ ∧ IsIso ψ := by
  have hpages : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ),
      IsIso ((φ.hom r hr).f ⟨p, q⟩) := by
    intro r
    refine Int.inductionOn' r 2 ?_ ?_ ?_
    · intro _
      exact h₂
    · intro r hr ih _ p q
      have : ∀ pq : ℤ × ℤ, IsIso ((φ.hom r hr).f pq) := fun pq ↦ ih hr pq.1 pq.2
      have : IsIso (φ.hom r hr) := HomologicalComplex.Hom.isIso_of_components _
      have : IsIso (HomologicalComplex.homologyMap (φ.hom r hr) ⟨p, q⟩) :=
        inferInstanceAs (IsIso ((HomologicalComplex.homologyFunctor C (c r) ⟨p, q⟩).map
          (φ.hom r hr)))
      have hc := φ.comm r (r + 1) ⟨p, q⟩ rfl hr
      have : IsIso ((E.iso r (r + 1) ⟨p, q⟩ rfl hr).hom ≫
          (φ.hom (r + 1) (by omega)).f ⟨p, q⟩) := by
        rw [← hc]
        infer_instance
      exact IsIso.of_isIso_comp_left (E.iso r (r + 1) ⟨p, q⟩ rfl hr).hom _
    · intro r hr _ hr'
      omega
  have ht := spectralSequence_finite_subobject_transport E E' φ h₂
    Z B π hZ₂ hB₂ hπ₂ hZ hB ι hι κ hκ hπ
    Z' B' π' hZ₂' hB₂' hπ₂' hZ' hB' ι' hι' κ' hκ' hπ' hpages
  refine ⟨hpages, ?_⟩
  intro p q
  have : IsIso ((φ.hom 2 le_rfl).f ⟨p, q⟩) := h₂ p q
  let e := Subobject.mapIsoToOrderIso (asIso ((φ.hom 2 le_rfl).f ⟨p, q⟩))
  have hz : ∀ r, 2 ≤ r → e (Z r p q) = Z' r p q := by
    intro r hr
    simpa only [Subobject.exists_iso_map, e, Subobject.mapIsoToOrderIso_apply, asIso_hom]
      using (ht r hr p q).1
  have hb : ∀ r, 2 ≤ r → e (B r p q) = B' r p q := by
    intro r hr
    simpa only [Subobject.exists_iso_map, e, Subobject.mapIsoToOrderIso_apply, asIso_hom]
      using (ht r hr p q).2
  have hzs : e '' {S | ∃ r : ℤ, 2 ≤ r ∧ S = Z r p q} =
      {S | ∃ r : ℤ, 2 ≤ r ∧ S = Z' r p q} := by
    ext S
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, hz r hr⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Z r p q, ⟨r, hr, rfl⟩, hz r hr⟩
  have hbs : e '' {S | ∃ r : ℤ, 2 ≤ r ∧ S = B r p q} =
      {S | ∃ r : ℤ, 2 ≤ r ∧ S = B' r p q} := by
    ext S
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, hb r hr⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨B r p q, ⟨r, hr, rfl⟩, hb r hr⟩
  have hzi : e (Zinf p q) = Zinf' p q := by
    apply IsGLB.unique _ (hZinf' p q)
    rw [← hzs]
    exact e.isGLB_image'.mpr (hZinf p q)
  have hbi : e (Binf p q) = Binf' p q := by
    apply IsLUB.unique _ (hBinf' p q)
    rw [← hbs]
    exact e.isLUB_image'.mpr (hBinf p q)
  exact subobject_quotient_iso ((φ.hom 2 le_rfl).f ⟨p, q⟩)
    (Zinf p q) (Binf p q) (Zinf' p q) (Binf' p q) hzi hbi

end CategoryTheory
