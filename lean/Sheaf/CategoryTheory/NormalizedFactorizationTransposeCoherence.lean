module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Normalized factorization transposes under changes of left adjoints

Source: blueprint main-20261015, lem-weil-finite-duality-site-comparison, second paragraph,
expanded factorization-conjugation step; Stacks Project, Tags 0037 and 0B65.
(blueprint: lem-sf-normalized-factorization-transpose-coherence)

The three statements give the normalized comparisons, their identity case, and their
composition case. All closure data are restricted to the specified full subcategory.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uP uQ vA vB vP vQ

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {P : Type uP} {Q : Type uQ}
  [Category.{vA} A] [Category.{vB} B] [Category.{vP} P] [Category.{vQ} Q]

private theorem transpose_conjugate
    {F F' : P ⥤ Q} {G G' : Q ⥤ P} (a : F ⊣ G) (b : F' ⊣ G')
    (e : F ≅ F') (X : P) (Y : Q) (h : F.obj X ⟶ Y) :
    b.homEquiv X Y (e.inv.app X ≫ h) =
      a.homEquiv X Y h ≫ (conjugateIsoEquiv a b e.symm).hom.app Y := by
  apply (b.homEquiv X Y).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, F'.map_comp,
    Category.assoc, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateEquiv_counit, ← Category.assoc,
    e.inv.naturality, Category.assoc, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply]

private theorem inverse_solution {X Y Z W : P} (g : X ≅ Y) (g' : X ≅ Z)
    (t : Y ⟶ Z) (hg : g'.hom = g.hom ≫ t) (rho : X ≅ W) :
    t ≫ g'.inv ≫ rho.hom = g.inv ≫ rho.hom := by
  apply (cancel_epi g.hom).mp
  rw [← Category.assoc, ← hg]
  simp

private theorem inverse_normalization {X Y Z W : Q}
    (r : X ≅ Y) (q : X ≅ Z) (q' : Y ≅ Z)
    (hq : r.hom ≫ q'.hom = q.hom) (h : X ⟶ W) :
    q'.inv ≫ r.inv ≫ h = q.inv ≫ h := by
  apply (cancel_epi q.hom).mp
  calc
    q.hom ≫ (q'.inv ≫ r.inv ≫ h) =
        (r.hom ≫ q'.hom) ≫ (q'.inv ≫ r.inv ≫ h) := by rw [hq]
    _ = q.hom ≫ (q.inv ≫ h) := by simp

/-- Compatible normalized closure squares determine the etale closure comparison and
transport the square, both adjunction transposes, the closure arrow, and normalized counit
solutions. Only the indicated Hom sets need injectivity.

Source: blueprint lem-weil-finite-duality-site-comparison, expanded factorization step;
Stacks Project, Tags 0037 and 0B65.
(blueprint: lem-sf-normalized-factorization-transpose-coherence)

Proof: (1) Compose the primed closure square with C_T(r_e), replace the comparison square,
and use q'_p r_p = q_p. Cancel B and apply the specified Hom-set injectivity to obtain
q'_e r_e = q_e. (2) The inverse comparison square identifies h' Delta' with C_T(h'_0).
The Hom formula of lem-sfb-adjunction-transport-left-iso identifies the etale transposes.
The inverse closure equation gives h' (q'_p)^{-1} = h q_p^{-1}.
(3) Apply lem-sfb-coherent-right-adjoint-comparisons to two indices, with left comparisons
identity and r_p. Its Hom-bijection formula identifies the pro-etale transposes via the
conjugate of r_p^{-1}, using def-weil-pbc-adjunction-conjugate.
(4) Set h = F_p(gamma) followed by the pro-etale counit and h_0 = the etale counit.
The first normalized equation is the square at H = R M. Transport of the etale adjunction
says its new counit is r_e^{-1} followed by its old counit, by the inverse Hom formula of
lem-weil-pbc-adjunction-of-natural-bijection. The second normalized equation and cancellation
of Delta' identify h' with F'_p(gamma') followed by the new counit. Transpose both sides:
the inverse Hom formula gives gamma' = gamma followed by t.
(5) Invert this equality and compose with the same arbitrary rho to obtain theta' t = theta.
The identity and composition assertions are stated separately below, following step (6).
-/
theorem normalized_factorization_transpose
    (CS : A ⥤ P) (CT : B ⥤ Q) (A0 : ObjectProperty A)
    {Fe Fe' Ee : A ⥤ B} {Fp Fp' Ep : P ⥤ Q}
    {R : B ⥤ A} {J J' : Q ⥤ P}
    (ae : Fe ⊣ R) (ap : Fp ⊣ J) (ap' : Fp' ⊣ J')
    (re : Fe ≅ Fe') (rp : Fp ≅ Fp')
    (delta : A0.ι ⋙ Fe ⋙ CT ≅ A0.ι ⋙ CS ⋙ Fp)
    (delta' : A0.ι ⋙ Fe' ⋙ CT ≅ A0.ι ⋙ CS ⋙ Fp')
    (closure : A0.ι ⋙ Ee ⋙ CT ≅ A0.ι ⋙ CS ⋙ Ep)
    (qe : A0.ι ⋙ Fe ≅ A0.ι ⋙ Ee) (qe' : A0.ι ⋙ Fe' ≅ A0.ι ⋙ Ee)
    (qp : A0.ι ⋙ CS ⋙ Fp ≅ A0.ι ⋙ CS ⋙ Ep)
    (qp' : A0.ι ⋙ CS ⋙ Fp' ≅ A0.ι ⋙ CS ⋙ Ep)
    (hsquare : ∀ L : A0.FullSubcategory,
      delta.hom.app L ≫ rp.hom.app (CS.obj L.obj) =
        CT.map (re.hom.app L.obj) ≫ delta'.hom.app L)
    (hclosure : ∀ L : A0.FullSubcategory,
      delta.hom.app L ≫ qp.hom.app L = CT.map (qe.hom.app L) ≫ closure.hom.app L)
    (hclosure' : ∀ L : A0.FullSubcategory,
      delta'.hom.app L ≫ qp'.hom.app L = CT.map (qe'.hom.app L) ≫ closure.hom.app L)
    (hqp : ∀ L : A0.FullSubcategory,
      rp.hom.app (CS.obj L.obj) ≫ qp'.hom.app L = qp.hom.app L)
    (hinj : ∀ L : A0.FullSubcategory,
      Function.Injective (CT.map : (Fe.obj L.obj ⟶ Ee.obj L.obj) → _)) :
    (∀ L : A0.FullSubcategory, re.hom.app L.obj ≫ qe'.hom.app L = qe.hom.app L) ∧
    (∀ (L : A0.FullSubcategory) (M : B)
      (h : Fp.obj (CS.obj L.obj) ⟶ CT.obj M) (h0 : Fe.obj L.obj ⟶ M),
      delta.hom.app L ≫ h = CT.map h0 →
        (delta'.hom.app L ≫ (rp.inv.app (CS.obj L.obj) ≫ h) =
          CT.map (re.inv.app L.obj ≫ h0)) ∧
        ((ae.ofNatIsoLeft re).homEquiv L.obj M (re.inv.app L.obj ≫ h0) =
          ae.homEquiv L.obj M h0) ∧
        (ap'.homEquiv (CS.obj L.obj) (CT.obj M) (rp.inv.app (CS.obj L.obj) ≫ h) =
          ap.homEquiv (CS.obj L.obj) (CT.obj M) h ≫
            (conjugateIsoEquiv ap ap' rp.symm).hom.app (CT.obj M)) ∧
        (qp'.inv.app L ≫ (rp.inv.app (CS.obj L.obj) ≫ h) = qp.inv.app L ≫ h)) ∧
    (∀ (M : B) (hH : A0 (R.obj M))
      (gamma : CS.obj (R.obj M) ≅ J.obj (CT.obj M))
      (gamma' : CS.obj (R.obj M) ≅ J'.obj (CT.obj M)),
      delta.hom.app ⟨R.obj M, hH⟩ ≫ Fp.map gamma.hom ≫ ap.counit.app (CT.obj M) =
        CT.map (ae.counit.app M) →
      delta'.hom.app ⟨R.obj M, hH⟩ ≫ Fp'.map gamma'.hom ≫ ap'.counit.app (CT.obj M) =
        CT.map ((ae.ofNatIsoLeft re).counit.app M) →
      (gamma'.hom = gamma.hom ≫ (conjugateIsoEquiv ap ap' rp.symm).hom.app (CT.obj M)) ∧
      (∀ (W : P) (rho : CS.obj (R.obj M) ≅ W),
        (conjugateIsoEquiv ap ap' rp.symm).hom.app (CT.obj M) ≫ gamma'.inv ≫ rho.hom =
          gamma.inv ≫ rho.hom)) := by
  have he (L : A0.FullSubcategory) :
      re.hom.app L.obj ≫ qe'.hom.app L = qe.hom.app L := by
    apply hinj L
    apply (cancel_mono (closure.hom.app L)).mp
    rw [CT.map_comp, Category.assoc, ← hclosure', ← Category.assoc,
      ← hsquare, Category.assoc, hqp, hclosure]
  have ht (L : A0.FullSubcategory) (M : B)
      (h : Fp.obj (CS.obj L.obj) ⟶ CT.obj M) (h0 : Fe.obj L.obj ⟶ M)
      (hh : delta.hom.app L ≫ h = CT.map h0) :
      delta'.hom.app L ≫ (rp.inv.app (CS.obj L.obj) ≫ h) =
        CT.map (re.inv.app L.obj ≫ h0) := by
    apply (cancel_epi (CT.map (re.hom.app L.obj))).mp
    rw [← Category.assoc, ← hsquare]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [hh, ← CT.map_comp]
    simp
  refine ⟨he, ?_, ?_⟩
  · intro L M h h0 hh
    refine ⟨ht L M h h0 hh, ?_, transpose_conjugate ap ap' rp _ _ h, ?_⟩
    · rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
      simp
    · exact inverse_normalization (rp.app (CS.obj L.obj)) (qp.app L) (qp'.app L)
        (hqp L) h
  · intro M hH gamma gamma' hg hg'
    have hh : Fp'.map gamma'.hom ≫ ap'.counit.app (CT.obj M) =
        rp.inv.app (CS.obj (R.obj M)) ≫
          (Fp.map gamma.hom ≫ ap.counit.app (CT.obj M)) := by
      apply (cancel_epi (delta'.hom.app ⟨R.obj M, hH⟩)).mp
      rw [hg', ht ⟨R.obj M, hH⟩ M _ _ hg]
      rfl
    have hgamma := transpose_conjugate ap ap' rp (CS.obj (R.obj M)) (CT.obj M)
      (Fp.map gamma.hom ≫ ap.counit.app (CT.obj M))
    rw [← hh] at hgamma
    change (ap'.homEquiv _ _) ((ap'.homEquiv _ _).symm gamma'.hom) =
      (ap.homEquiv _ _) ((ap.homEquiv _ _).symm gamma.hom) ≫ _ at hgamma
    simp only [Equiv.apply_symm_apply] at hgamma
    exact ⟨hgamma, fun W rho ↦ inverse_solution gamma gamma' _ hgamma rho⟩

/-- Identity changes leave the adjunction, conjugate, transported arrows, counit solution,
and its inverse followed by any fixed rho unchanged.

Source: blueprint lem-weil-finite-duality-site-comparison, expanded factorization step (6);
Stacks Project, Tags 0037 and 0B65.
(blueprint: lem-sf-normalized-factorization-transpose-coherence)

Proof: step (6) specializes the transport Hom formula to the identity. The units and counits
are unchanged. Conjugation sends identity to identity by def-weil-pbc-adjunction-conjugate.
The inverse identity components act as identities on h and h_0; composing gamma with the
identity gives the same gamma and the same inverse followed by rho. These are exactly the
identity specializations of all comparisons in normalized_factorization_transpose.
-/
theorem normalized_factorization_transpose_identity
    (CS : A ⥤ P) (CT : B ⥤ Q) {Fe : A ⥤ B} {Fp : P ⥤ Q}
    {R : B ⥤ A} {J : Q ⥤ P} (ae : Fe ⊣ R) (ap : Fp ⊣ J) :
    ae.ofNatIsoLeft (Iso.refl Fe) = ae ∧
    conjugateIsoEquiv ap ap (Iso.refl Fp) = Iso.refl J ∧
    (∀ (L : A) (M : B) (h : Fp.obj (CS.obj L) ⟶ CT.obj M) (h0 : Fe.obj L ⟶ M),
      (Iso.refl Fp).inv.app (CS.obj L) ≫ h = h ∧
      (Iso.refl Fe).inv.app L ≫ h0 = h0) ∧
    (∀ (M : B) (gamma : CS.obj (R.obj M) ≅ J.obj (CT.obj M))
      (W : P) (rho : CS.obj (R.obj M) ≅ W),
      gamma.hom ≫ (conjugateIsoEquiv ap ap (Iso.refl Fp)).hom.app (CT.obj M) =
        gamma.hom ∧
      (conjugateIsoEquiv ap ap (Iso.refl Fp)).hom.app (CT.obj M) ≫ gamma.inv ≫ rho.hom =
        gamma.inv ≫ rho.hom) := by
  have ha : ae.ofNatIsoLeft (Iso.refl Fe) = ae := by
    apply Adjunction.ext
    simp [Adjunction.ofNatIsoLeft_unit]
  have hc : conjugateIsoEquiv ap ap (Iso.refl Fp) = Iso.refl J := by
    apply Iso.ext
    exact conjugateEquiv_id ap
  refine ⟨ha, hc, ?_, ?_⟩
  · intro L M h h0
    simp
  · intro M gamma W rho
    simp [hc]

/-- Successive compatible changes give the same squares, normalized closure comparisons,
transported arrows, transposes, counit solutions and theta maps as their composite.

Source: blueprint lem-weil-finite-duality-site-comparison, expanded factorization step (6);
Stacks Project, Tags 0037 and 0B65.
(blueprint: lem-sf-normalized-factorization-transpose-coherence)

Proof: substitute the two comparison squares to obtain the composite square. Compose the
two closure normalization equations and cancel the intermediate isomorphisms; the same
calculation gives the etale closure normalization after the Hom-set cancellation in step (1).
The transport Hom formula of lem-sfb-adjunction-transport-left-iso composes, so the two
transported adjunctions coincide. The inverse of re followed by se is se inverse followed
by re inverse, and similarly for rp,sp; associativity gives the two arrow formulas.
By def-weil-pbc-adjunction-conjugate, conjugation of the composite inverse is the composite
of conjugates. Apply the transpose formula of steps (2)--(3) twice to identify the successive
transposes with the composite transpose. Finally step (4), twice, gives gamma'' = gamma'
followed by u = gamma followed by t followed by u; invert this and cancel to give
 theta'' u t = theta' t = theta, always with the same arbitrary rho.
-/
theorem normalized_factorization_transpose_comp
    (CS : A ⥤ P) (CT : B ⥤ Q) (A0 : ObjectProperty A)
    {Fe Fe' Fe'' Ee : A ⥤ B} {Fp Fp' Fp'' Ep : P ⥤ Q}
    {R : B ⥤ A} {J J' J'' : Q ⥤ P}
    (ae : Fe ⊣ R) (ap : Fp ⊣ J) (ap' : Fp' ⊣ J') (ap'' : Fp'' ⊣ J'')
    (re : Fe ≅ Fe') (se : Fe' ≅ Fe'') (rp : Fp ≅ Fp') (sp : Fp' ≅ Fp'')
    (delta : A0.ι ⋙ Fe ⋙ CT ≅ A0.ι ⋙ CS ⋙ Fp)
    (delta' : A0.ι ⋙ Fe' ⋙ CT ≅ A0.ι ⋙ CS ⋙ Fp')
    (delta'' : A0.ι ⋙ Fe'' ⋙ CT ≅ A0.ι ⋙ CS ⋙ Fp'')
    (qe : A0.ι ⋙ Fe ≅ A0.ι ⋙ Ee) (qe' : A0.ι ⋙ Fe' ≅ A0.ι ⋙ Ee)
    (qe'' : A0.ι ⋙ Fe'' ≅ A0.ι ⋙ Ee)
    (qp : A0.ι ⋙ CS ⋙ Fp ≅ A0.ι ⋙ CS ⋙ Ep)
    (qp' : A0.ι ⋙ CS ⋙ Fp' ≅ A0.ι ⋙ CS ⋙ Ep)
    (qp'' : A0.ι ⋙ CS ⋙ Fp'' ≅ A0.ι ⋙ CS ⋙ Ep)
    (hsquare : ∀ L : A0.FullSubcategory,
      delta.hom.app L ≫ rp.hom.app (CS.obj L.obj) =
        CT.map (re.hom.app L.obj) ≫ delta'.hom.app L)
    (hsquare' : ∀ L : A0.FullSubcategory,
      delta'.hom.app L ≫ sp.hom.app (CS.obj L.obj) =
        CT.map (se.hom.app L.obj) ≫ delta''.hom.app L)
    (hqe : ∀ L : A0.FullSubcategory,
      re.hom.app L.obj ≫ qe'.hom.app L = qe.hom.app L)
    (hqe' : ∀ L : A0.FullSubcategory,
      se.hom.app L.obj ≫ qe''.hom.app L = qe'.hom.app L)
    (hqp : ∀ L : A0.FullSubcategory,
      rp.hom.app (CS.obj L.obj) ≫ qp'.hom.app L = qp.hom.app L)
    (hqp' : ∀ L : A0.FullSubcategory,
      sp.hom.app (CS.obj L.obj) ≫ qp''.hom.app L = qp'.hom.app L) :
    (∀ L : A0.FullSubcategory,
      (delta.hom.app L ≫ (rp ≪≫ sp).hom.app (CS.obj L.obj) =
        CT.map ((re ≪≫ se).hom.app L.obj) ≫ delta''.hom.app L) ∧
      ((re ≪≫ se).hom.app L.obj ≫ qe''.hom.app L = qe.hom.app L) ∧
      ((rp ≪≫ sp).hom.app (CS.obj L.obj) ≫ qp''.hom.app L = qp.hom.app L)) ∧
    (ae.ofNatIsoLeft re).ofNatIsoLeft se = ae.ofNatIsoLeft (re ≪≫ se) ∧
    (conjugateIsoEquiv ap ap' rp.symm ≪≫ conjugateIsoEquiv ap' ap'' sp.symm =
      conjugateIsoEquiv ap ap'' (rp ≪≫ sp).symm) ∧
    (∀ (L : A0.FullSubcategory) (M : B)
      (h : Fp.obj (CS.obj L.obj) ⟶ CT.obj M) (h0 : Fe.obj L.obj ⟶ M),
      (sp.inv.app (CS.obj L.obj) ≫ (rp.inv.app (CS.obj L.obj) ≫ h) =
        (rp ≪≫ sp).inv.app (CS.obj L.obj) ≫ h) ∧
      (se.inv.app L.obj ≫ (re.inv.app L.obj ≫ h0) = (re ≪≫ se).inv.app L.obj ≫ h0) ∧
      ((ae.ofNatIsoLeft (re ≪≫ se)).homEquiv L.obj M
        ((re ≪≫ se).inv.app L.obj ≫ h0) = ae.homEquiv L.obj M h0) ∧
      (ap''.homEquiv (CS.obj L.obj) (CT.obj M)
        ((rp ≪≫ sp).inv.app (CS.obj L.obj) ≫ h) =
        ap.homEquiv (CS.obj L.obj) (CT.obj M) h ≫
          (conjugateIsoEquiv ap ap' rp.symm).hom.app (CT.obj M) ≫
          (conjugateIsoEquiv ap' ap'' sp.symm).hom.app (CT.obj M)) ∧
      (qp''.inv.app L ≫ (rp ≪≫ sp).inv.app (CS.obj L.obj) ≫ h = qp.inv.app L ≫ h)) ∧
    (∀ (M : B) (gamma : CS.obj (R.obj M) ≅ J.obj (CT.obj M))
      (gamma' : CS.obj (R.obj M) ≅ J'.obj (CT.obj M))
      (gamma'' : CS.obj (R.obj M) ≅ J''.obj (CT.obj M)),
      gamma'.hom = gamma.hom ≫ (conjugateIsoEquiv ap ap' rp.symm).hom.app (CT.obj M) →
      gamma''.hom = gamma'.hom ≫ (conjugateIsoEquiv ap' ap'' sp.symm).hom.app (CT.obj M) →
      (gamma''.hom = gamma.hom ≫
        (conjugateIsoEquiv ap ap'' (rp ≪≫ sp).symm).hom.app (CT.obj M)) ∧
      (∀ (W : P) (rho : CS.obj (R.obj M) ≅ W),
        ((conjugateIsoEquiv ap' ap'' sp.symm).hom.app (CT.obj M) ≫
          gamma''.inv ≫ rho.hom = gamma'.inv ≫ rho.hom) ∧
        ((conjugateIsoEquiv ap ap'' (rp ≪≫ sp).symm).hom.app (CT.obj M) ≫
          gamma''.inv ≫ rho.hom = gamma.inv ≫ rho.hom))) := by
  have hc : conjugateIsoEquiv ap ap' rp.symm ≪≫
      conjugateIsoEquiv ap' ap'' sp.symm =
      conjugateIsoEquiv ap ap'' (rp ≪≫ sp).symm := by
    apply Iso.ext
    exact conjugateEquiv_comp ap ap' ap'' rp.inv sp.inv
  have hqc (L : A0.FullSubcategory) :
      (rp ≪≫ sp).hom.app (CS.obj L.obj) ≫ qp''.hom.app L = qp.hom.app L := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    rw [hqp', hqp]
  refine ⟨?_, ?_, hc, ?_, ?_⟩
  · intro L
    refine ⟨?_, ?_, hqc L⟩
    · simp only [Iso.trans_hom, NatTrans.comp_app, CT.map_comp]
      rw [← Category.assoc, hsquare, Category.assoc, hsquare', ← Category.assoc]
    · simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
      rw [hqe', hqe]
  · apply Adjunction.ext
    ext X
    simp [Adjunction.ofNatIsoLeft_unit, Category.assoc]
  · intro L M h h0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Category.assoc]
    · simp [Category.assoc]
    · rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
      simp
    · rw [transpose_conjugate ap ap'' (rp ≪≫ sp)]
      rw [← hc]
      simp only [Iso.trans_hom, NatTrans.comp_app]
    · exact inverse_normalization ((rp ≪≫ sp).app (CS.obj L.obj))
        (qp.app L) (qp''.app L) (hqc L) h
  · intro M gamma gamma' gamma'' hg hg'
    have hgc : gamma''.hom = gamma.hom ≫
        (conjugateIsoEquiv ap ap'' (rp ≪≫ sp).symm).hom.app (CT.obj M) := by
      rw [hg', hg, ← hc]
      simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
    exact ⟨hgc, fun W rho ↦ ⟨inverse_solution gamma' gamma'' _ hg' rho,
      inverse_solution gamma gamma'' _ hgc rho⟩⟩

end CategoryTheory
