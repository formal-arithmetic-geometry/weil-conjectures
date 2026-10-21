# AlgebraicGeometry.principalSubsetHorizontalFaceCoordinate

## Reason

Complete the zero-hole retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate. The adopted
source twin already proves precisely the same theorem. The duplicate copy introduces
the same public constant, preventing both copies from coexisting in an environment.

## Old

The duplicate module declares the following signature verbatim:

```lean
theorem principalSubsetHorizontalFaceCoordinate
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (J : CochainComplex (Spec (.of A)).Modules ℤ) :
    let V := principalSubsetUnion A r f
    let U : Fin r → V.toScheme.Opens := fun i ↦ V.ι ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)
    let D := principalSubsetOpen A r f
    ∀ (hle : ∀ (S : Finset (Fin r)) (j : Fin r), D S ≤ D (S.erase j))
      (he : ∀ (S : Finset (Fin r)) (j : Fin r), j ∈ S → ∀ n : ℤ,
        n + 1 - ((S.erase j).card : ℤ) = n + 1 + 1 - (S.card : ℤ))
      (n : ℤ) (S₀ : {S : Finset (Fin r) // S.Nonempty})
      (x : (modulesSpecToSheaf.obj (J.X (n + 1 - (S₀.val.card : ℤ)))).obj.obj
        (op (D S₀.val))),
      let p := S₀.val.card - 1
      let q := n + 1 - (S₀.val.card : ℤ)
      let P := alternatingCechModulePresheaf.obj ((principalSubsetRestriction A r f J).X q)
      ∀ (S : {S : Finset (Fin r) // S.Nonempty}) (hcard : S.val.card = p + 2),
      HEq (((alternatingCechDifferential U P p).hom
          (Pi.single (principalSubsetTuple r S₀)
            ((principalSubsetSectionTransport A r f (J.X q) S₀).hom x)))
          (S.val.orderEmbOfFin hcard))
        ((principalSubsetSectionTransport A r f
          (J.X (n + 1 + 1 - (S.val.card : ℤ))) S).hom (
          ∑ j : S.val, if h : (S.val.erase j.val).Nonempty then
            (-1 : A) ^ ((S.val.filter (fun i ↦ i < j.val)).card) •
              (modulesSpecToSheaf.obj (J.X (n + 1 + 1 - (S.val.card : ℤ)))).obj.map
                (homOfLE (hle S.val j.val)).op
                ((modulesSpecToSheaf.map
                  (eqToHom (congrArg J.X (he S.val j.val j.property n)))).hom.app
                    (op (D (S.val.erase j.val)))
                    ((Pi.single S₀ x : principalSubsetCoordinates A r f J n)
                      ⟨S.val.erase j.val, h⟩))
          else 0))
```

## New

The same signature is supplied by the untouched adopted-source module
WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate.
The old module is withdrawn through deleted.txt. Its DAG node is retained and its
lean attachment points to the source theorem. The mathematical statement, all
statement/proof dependency edges, proof steps, and unit route are preserved.

A server-compiled example repeats the entire old signature and closes with
`exact principalSubsetHorizontalFaceCoordinate A r f J` after importing only the
source twin. The replacement theorem's printed axioms are exactly propext,
Classical.choice and Quot.sound. This verifies all binders and universes as well
as the degree, sign and restriction conventions. In particular the small-rank
vacuous cases and arbitrary coefficient complexes are unchanged.

The two files differ only in header, one proof import, and explicit universe
annotations on three private helpers; the public signature is identical. No
source-library declaration, attribute, definition, or import is changed.
No target definition or meaning changes; target review is not reopened.

## Users

Current source and quarantine scans find no importer of the retired Sheaf module.
The inventory's former Sheaf.HorizontalFaces consumer is already absent; its DAG
node is attached to the source HorizontalFaces module. That existing parent already
imports the replacement and calls the same theorem in its final proof branch.
The parent was compiled unchanged through lcompile.py (28.6 s).

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate | P4 | Withdraw duplicate. |
| WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate | unmodified source | Supplies the exact original theorem. |
| WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaces | unmodified source | Existing parent already uses the source theorem; compiled unchanged. |

The only DAG parent is lem-sc-principal-open-cech-subset-horizontal-faces. Its
proof_deps and proof step still cite the retained coordinate node, now realized by
the source declaration. Nothing mathematical is pruned. No consumer adaptation is
needed and there are no forced adaptations.

## Status

landed 20261021T111406-L-102852 2026-10-21 (merge of deliver/P4/Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate)
