# WeilConjectures.IsAdicPurityEtaleDiagonal

## Reason

Kernel profiling found repeated expensive checking of derived-category instances
and degree-zero functor objects. Add adicPurityEtaleDiagonalModel over an arbitrary
coefficient ring, with generic ordered-power source and target written explicitly.
Its body is exactly the existing adicPurityDiagonalGeneric applied to the original
unit isomorphism. Use the existing Etale.ordinaryFiniteDegreeZero stable object
interface in the three etale diagonal signatures: its body is exactly the old
singleFunctor.obj expression. Both changes are definitional substitutions:
the prescribed comparison, existing types and mathematical meaning stay unchanged.
No hypothesis, conclusion or object construction changes.
No source-library module changes.

## Old

    def IsAdicPurityEtaleDiagonal (r : ℕ)
        (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
        (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ)
        (e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d ≅
            ((DerivedCategory.singleFunctor _ 0).obj
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧) : Prop :=
      HEq e (adicPurityDiagonalGeneric
            (Etale.ordinaryFiniteConstant (finiteTateCoefficient l E n) T)
            (finiteEtaleTateLine T (l ^ (r + 1)) (finiteTateCoefficient l E n) hA)
            (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T)
            (adicPurityEtaleGenericPower_flat l E n T r hT hA) d)

    theorem adicPurityEtaleDiagonal_existsUnique (r : ℕ)
        (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
        (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
        ∃! e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d ≅
            ((DerivedCategory.singleFunctor _ 0).obj
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧,
          IsAdicPurityEtaleDiagonal l E n T r hT hA d e

    def adicPurityEtaleDiagonal (r : ℕ)
        (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
        (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
        Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d ≅
            ((DerivedCategory.singleFunctor _ 0).obj
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧ :=
      (adicPurityEtaleDiagonal_existsUnique l E n T r hT hA d).choose

## New

    def IsAdicPurityEtaleDiagonal (r : ℕ)
        (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
        (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ)
        (e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d ≅
            (Etale.ordinaryFiniteDegreeZero (finiteTateCoefficient l E n) T
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧) : Prop :=
      HEq e (adicPurityEtaleDiagonalModel (finiteTateCoefficient l E n) (l ^ (r + 1)) hA T
        (adicPurityEtaleGenericPower_flat l E n T r hT hA) d)

    theorem adicPurityEtaleDiagonal_existsUnique (r : ℕ)
        (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
        (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
        ∃! e : Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d ≅
            (Etale.ordinaryFiniteDegreeZero (finiteTateCoefficient l E n) T
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧,
          IsAdicPurityEtaleDiagonal l E n T r hT hA d e

    def adicPurityEtaleDiagonal (r : ℕ)
        (hT : IsUnit ((l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
        (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (d : ℕ) :
        Etale.affineLinearBaseCoefficient (finiteTateCoefficient l E n)
          (l ^ (r + 1)) hA T d ≅
            (Etale.ordinaryFiniteDegreeZero (finiteTateCoefficient l E n) T
              (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA d))⟦2 * (d : ℤ)⟧ :=
      (adicPurityEtaleDiagonal_existsUnique l E n T r hT hA d).choose

The new model is the same generic diagonal, with explicit concrete object types:

    @[no_expose] def adicPurityEtaleDiagonalModel (A : Type (u + 1)) [CommRing A]
        (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
        (hF : ∀ d : ℕ, ObjectProperty.flat (adicPurityPower
          (Etale.ordinaryFiniteConstant A T) (finiteEtaleTateLine T N A hA) d)) (d : ℕ) :
        adicPurityShiftedPower (Etale.ordinaryFiniteConstant A T)
          (finiteEtaleTateLine T N A hA) d ≅
            (Etale.ordinaryFiniteDegreeZero A T
              (adicPurityPower (Etale.ordinaryFiniteConstant A T)
                (finiteEtaleTateLine T N A hA) d))⟦2 * (d : ℤ)⟧ :=
      adicPurityDiagonalGeneric (Etale.ordinaryFiniteConstant A T)
        (finiteEtaleTateLine T N A hA)
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T) hF d
    
Unfolding adicPurityEtaleDiagonalModel and Etale.ordinaryFiniteDegreeZero restores
all three old types and the predicate's old body. The node's Lean attachment
includes this performance interface.

## Users

The downstream.py declaration-use searches for all three changed names report only
the item itself as a direct user. There are 347 transitive importing modules, with
no changes required because the original types and definitional meaning are
preserved. No outside module directly uses the changed declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPurityRootComparisons | N2 | Uses the stable degree-zero interface and typed generic model; proof transports the model across two recursion equalities. |

No other file is adapted. Existing target signatures and all definitions they use
are definitionally unchanged. The independent delivery review can verify this
by unfolding the two interfaces.

## Status

landed 20261026T070345-L-3558301 2026-10-26 (merge of deliver/N2/Sheaf.Paper.AdicPurityRootComparisons)
