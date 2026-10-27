# AlgebraicGeometry.Scheme.CoefficientTensorTransport.tensorComparison_compatibility

## Reason

The old Lean signature asserted compatibility for arbitrary isomorphisms rho and b, although its docstring and source required normalized ones. Replacing rho by its negative negates just the right side. With nonzero integer coefficients and degree-zero rank-one modules on a nonempty geometric point, the invertible tensor comparison is distinct from its negative. This is a false intermediate statement, not a target statement. The replacement constructs rho from the ordinary chain comparison and fixes b to the canonical one.

## Old

```lean
theorem tensorComparison_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY : ProEtaleTensorModel Y R)
    (z : ProEtaleTensorModel X
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (aX : ProEtaleTensorModel X S)
    (rho : ((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)) ⋙ z.tensor ≅
      aX.tensor ⋙ pbcDerivedRestrict c.hom)
    (b : proEtaleRingDerivedPullback f R S c ⋙ pbcDerivedRestrict c.hom ≅
      proEtaleRingDerivedPullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _))
    (F G : DerivedCategory (proEtaleRingModules Y R)) :
      b.hom.app (aY.tensor.obj (F, G)) ≫
          (proEtaleCanonicalTensorComparison f R
            ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
            (Iso.refl _) aY z).hom.app (F, G) =
        (pbcDerivedRestrict c.hom).map
            ((proEtaleCanonicalTensorComparison f R S c aY aX).hom.app (F, G)) ≫
          rho.inv.app ((proEtaleRingDerivedPullback f R S c).obj F,
            (proEtaleRingDerivedPullback f R S c).obj G) ≫
          z.tensor.map (Prod.mkHom (b.hom.app F) (b.hom.app G))
```

## New

```lean
theorem tensorComparison_compatibility {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY : ProEtaleTensorModel Y R)
    (z : ProEtaleTensorModel X
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (aX : ProEtaleTensorModel X S) :
    ∃ rho : ((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)) ⋙ z.tensor ≅
        aX.tensor ⋙ pbcDerivedRestrict c.hom,
      ∀ F G : DerivedCategory (proEtaleRingModules Y R),
        (pullback f R S c).hom.app (aY.tensor.obj (F, G)) ≫
            (proEtaleCanonicalTensorComparison f R
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
              (Iso.refl _) aY z).hom.app (F, G) =
          (pbcDerivedRestrict c.hom).map
              ((proEtaleCanonicalTensorComparison f R S c aY aX).hom.app (F, G)) ≫
            rho.inv.app ((proEtaleRingDerivedPullback f R S c).obj F,
              (proEtaleRingDerivedPullback f R S c).obj G) ≫
            z.tensor.map (Prod.mkHom
              ((pullback f R S c).hom.app F)
              ((pullback f R S c).hom.app G))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleCoefficientTensorCompatibility | J1 | Construct normalized rho by representative descent and prove its geometric compatibility. |
| Sheaf.Paper.ProEtaleCoefficientTensorTransport | unclaimed | Preserve tensorComparison signature; replace the invalid arbitrary-witness proof by the repaired theorem. Move identityRestriction and pullback verbatim to the coefficient-pullback support module and publicly re-export them. |
| Sheaf.Paper.CompletedTensorProjectionCoefficientTransport | not changed | Direct importer of the parent; no signature or definition change reaches it. Compiled unchanged against the packet; temporary verification copy excluded from delivery. |

The only direct importer of the changed compatibility module is ProEtaleCoefficientTensorTransport. The only declaration use is its final proof line. The compatibility signature changes as documented above. No target statement, universe, existing public declaration name, existing definition body, typeclass instance or global attribute is changed. The moved definitions have exactly their old fully qualified names and bodies. Because `pullback` is now owned by the node
`lem-pbc-coefficient-pullback-factorization`, that node is added to the `stmt_deps` of
the parent node `lem-pbc-coefficient-restriction-tensor-comparison` (reviewer fix); its
statement text and Lean statement are unchanged. No source-library module is changed.

## Status

landed 20261027T072146-L-2804008 2026-10-27 (merge of deliver/J1/Sheaf.Paper.ProEtaleCoefficientTensorCompatibility)
