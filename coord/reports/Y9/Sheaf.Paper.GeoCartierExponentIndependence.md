## What changed

Proved `SheafOfModules.GeoCartierExponent.projection_comp` in
`Sheaf.Paper.GeoCartierExponentIndependence`. Functoriality of the constant-sheaf
functor reduces the triangle to equality of the two ring maps. After unwrapping
ULift, `map_intCast` proves that reduction from Z through Z/m to Z/n is direct
reduction to Z/n. The statement and all original imports are unchanged. A local
unused-section-variable linter setting preserves the existing theorem signature.

The remote compiler accepted the module without errors or warnings (3.0 seconds).
This is a partial delivery: the second theorem is unchanged.

## Proved and sorry left

Closed one of the original two holes:
`SheafOfModules.GeoCartierExponent.projection_comp`.

One hole remains, unchanged:
`SheafOfModules.GeoCartierExponent.geoCartier_exponent_independence`
(node `lem-geo-cartier-exponent-independence`). No holes were added and no theorem
was split off. Its docstring and node retain the complete eight-step proof plan.

Exploration constructed the integral quotient comparison by the cokernel universal
property and the integral torsion comparison by the kernel universal property;
these calculations and a separate transitivity-unit helper typechecked in a
scratch compilation (3.1 seconds).
They remain in scratch work and are not part of this delivery. To finish the main
proof, one must descend these comparisons to residue-linear maps, show the ordinary
tensor maps are isomorphisms by the local lifting calculations of steps 7--8, and
identify the derived comparisons by the two normalized adjunctions and Kummer
boundary naturality (steps 2--6). No statement was replaced by an equivalent hole.

## No longer needed

None. No import, module or dependency is pruned: the remaining main theorem still
has the original proof plan and needs its recorded dependencies. The coefficient
triangle proof itself uses only the existing constant-sheaf functoriality and the
ring-homomorphism integer-cast formula.

## Where the brief, the DAG or earlier work was wrong

The quotient-unit normalization required by step 1 is already an explicit field
`Identifications.quotient_unit` of the existing reduction interface, so it need
not be rederived from a K-flat resolution in this consumer. This observation is
not a route change in the delivered proof of the main theorem, which is untouched.
The server occasionally returned no answer before the remote compile deadline;
retrying obtained a clean compilation. No project or launcher tool was changed.

The following scratch lemmas compiled together, with the item's existing context
and imports. They are included here as reusable work for the remaining theorem;
they are not additional declarations in the delivered library. The first two go
before the derived-category variables, and the last goes after `ordinarySingle`.

```lean
omit [EssentiallySmall.{r} C] in
private theorem integral_beta_exists (h : n ∣ m)
    (Pm : DivisibleReduction.Presentation (J := J) m)
    (Pn : DivisibleReduction.Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) :
    ∃ b : (restriction J m).obj Pm.H ⟶ (restriction J n).obj Pn.H,
      b ≫ Pn.i = (m / n) • (Pm.i ≫ eqToHom hB) := by
  have : Mono Pn.i := Pn.kummer.mono_f
  have hw : ((m / n) • (Pm.i ≫ eqToHom hB)) ≫ (n • 𝟙 Pn.S.X₁) = 0 := by
    rw [Preadditive.comp_nsmul, Category.comp_id, smul_smul,
      Nat.mul_div_cancel' h]
    rw [← Preadditive.nsmul_comp]
    have hi : m • Pm.i = 0 := by
      simpa only [Preadditive.comp_nsmul, Category.comp_id] using Pm.wi
    rw [hi, zero_comp]
  exact ⟨Pn.kummer.exact.lift _ hw, Pn.kummer.exact.lift_f _ hw⟩

omit [EssentiallySmall.{r} C] in
private theorem integral_rho_exists (h : n ∣ m)
    (Pm : DivisibleReduction.Presentation (J := J) m)
    (Pn : DivisibleReduction.Presentation (J := J) n)
    (hF : Pm.S.X₃ = Pn.S.X₃) :
    ∃ q : (restriction J m).obj Pm.Q ⟶ (restriction J n).obj Pn.Q,
      Pm.p ≫ q = eqToHom hF ≫ Pn.p := by
  have : Epi Pm.p := Pm.quotient.epi_g
  have hw : (m • 𝟙 Pm.S.X₃) ≫ (eqToHom hF ≫ Pn.p) = 0 := by
    have hp : n • Pn.p = 0 := by
      simpa only [Preadditive.nsmul_comp, Category.id_comp] using Pn.wp
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Preadditive.comp_nsmul]
    have hp' : m • Pn.p = 0 := calc
      m • Pn.p = ((m / n) * n) • Pn.p :=
        congrArg (fun k : ℕ ↦ k • Pn.p) (Nat.div_mul_cancel h).symm
      _ = 0 := by rw [mul_smul, hp, smul_zero]
    rw [hp', comp_zero]
  exact ⟨Pm.quotient.exact.desc _ hw, Pm.quotient.exact.g_desc _ hw⟩

set_option backward.isDefEq.respectTransparency false in
private theorem transitivity_unit (h : n ∣ m)
    (Dm : DerivedChangeOfRingsCochainModel (projection J m))
    (Dn : DerivedChangeOfRingsCochainModel (projection J n))
    (Dmn : DerivedChangeOfRingsCochainModel (residueProjection (J := J) h))
    (X : DerivedCategory (Integral J)) :
    (sheafScalarDerivedAdjunction (projection J m) Dm).unit.app X ≫
      (derivedRestriction m).map
        ((sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn).unit.app
          (Dm.T.obj X)) ≫
      (derivedRestrictionComp (J := J) h).hom.app (Dmn.T.obj (Dm.T.obj X)) ≫
      (derivedRestriction n).map ((transitivity h Dm Dn Dmn).hom.app X) =
    (sheafScalarDerivedAdjunction (projection J n) Dn).unit.app X := by
  simpa only [transitivity, derivedRestriction, restriction, Functor.comp_obj,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Category.assoc] using
    (Adjunction.unit_leftAdjointUniq_hom_app
      (((sheafScalarDerivedAdjunction (projection J m) Dm).comp
        (sheafScalarDerivedAdjunction (residueProjection (J := J) h) Dmn)).ofNatIsoRight
          (derivedRestrictionComp (J := J) h))
      (sheafScalarDerivedAdjunction (projection J n) Dn) X)
```

The boundary comparison of step 5 also compiles without warnings (3.3 seconds
for the complete scratch file). It uses only short-exact-triangle naturality:

```lean
omit [EssentiallySmall.{r} C] [HasDerivedCategory.{wM} (Residue J m)]
  [HasDerivedCategory.{wN} (Residue J n)] in
private theorem integral_beta_boundary (h : n ∣ m)
    (Pm : DivisibleReduction.Presentation (J := J) m)
    (Pn : DivisibleReduction.Presentation (J := J) n)
    (hB : Pm.S.X₁ = Pn.S.X₁) :
    ∃ b : (restriction J m).obj Pm.H ⟶ (restriction J n).obj Pn.H,
      b ≫ Pn.i = (m / n) • (Pm.i ≫ eqToHom hB) ∧
      Pm.kummer.singleδ ≫
        ((DerivedCategory.singleFunctor (Integral J) 0).map b)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor (Integral J) 0).map (eqToHom hB) ≫
        Pn.kummer.singleδ := by
  obtain ⟨b, hb⟩ := integral_beta_exists h Pm Pn hB
  let f : ShortComplex.mk Pm.i (m • 𝟙 Pm.S.X₁) Pm.wi ⟶
      ShortComplex.mk Pn.i (n • 𝟙 Pn.S.X₁) Pn.wi :=
    { τ₁ := b
      τ₂ := (m / n) • eqToHom hB
      τ₃ := eqToHom hB
      comm₁₂ := by
        simpa only [Preadditive.comp_nsmul] using hb
      comm₂₃ := by
        simp only [Preadditive.comp_nsmul,
          Preadditive.nsmul_comp, Category.comp_id, Category.id_comp, smul_smul]
        exact congrArg (fun k : ℕ ↦ k • eqToHom hB) (Nat.mul_div_cancel' h) }
  refine ⟨b, hb, ?_⟩
  exact (ShortComplex.ShortExact.singleTriangle.map Pm.kummer Pn.kummer f).comm₃
```

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
