# AlgebraicGeometry.Scheme.AffineCoordinateStrictLocal comparison data extraction

## Reason

Isolate the genuinely smaller polynomial closed-fibre comparison from the geometric
coordinate-zero construction. A split lemma cannot import the original item while the
item imports that lemma. Move the 12 existing data declarations, unchanged, into the
new AffineCoordinateStrictLocalData module and publicly import it from the original
module. The original Model and exists_model declarations stay in the item. All 14
original signatures and all 12 data bodies are preserved verbatim; only the moved
docstrings receive the new data node's blueprint identifier. No hypothesis, conclusion,
instance or attribute changes. No source-library file is changed.

No direct Lean importer of the original module exists in the current source snapshot;
this is a DAG dependency of an unfinished parent. That parent and all its attachments
are preserved. The new public import re-exports exactly the existing data declarations
and their public imports, so future consumers keep the same names and types.
The meaning of definitions used by targets is unchanged.

## Old

The following signatures were in
lean/Sheaf/AlgebraicGeometry/AffineCoordinateStrictLocalModel.lean:

```lean
abbrev Index (r : ℕ)

def projection {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) : V ⟶ S

def ringMap {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : y = x ≫ g) : strictHenselizationRing y →+* strictHenselizationRing x

def Base {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)

def baseMap {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) : Base r e v →+* strictHenselizationRing v

def coordinate {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) (i : Index.{u} r) : strictHenselizationRing v

def coordinateIdeal {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) (K : Set (Index.{u} r)) : Ideal (strictHenselizationRing v)

def inclusion {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r)) : AffineSpace {i : Index.{u} r // i ∉ K} S ⟶ V

def fibreIdeal {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) [IsLocalRing (Base r e v)] : Ideal (strictHenselizationRing v)

def PolynomialRing {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) [IsLocalRing (Base r e v)]

def polynomialIdeal {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) [IsLocalRing (Base r e v)] (K : Set (Index.{u} r)) : Ideal (PolynomialRing r e v)

structure FibreModels (A B P : CommRingCat.{u}) [IsLocalRing A] (E : Type u) (K : Set E) (I J : Ideal B) (L : Ideal P) (a : A →+* B) (c : A →+* P) (t : E → B) (x : E → P) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (εA : A →+* Ω) (εB : B →+* Ω)
```

## New

The same signatures and bodies now occur in
lean/Sheaf/AlgebraicGeometry/AffineCoordinateStrictLocalData.lean:

```lean
abbrev Index (r : ℕ)

def projection {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) : V ⟶ S

def ringMap {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : y = x ≫ g) : strictHenselizationRing y →+* strictHenselizationRing x

def Base {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)

def baseMap {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) : Base r e v →+* strictHenselizationRing v

def coordinate {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) (i : Index.{u} r) : strictHenselizationRing v

def coordinateIdeal {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) (K : Set (Index.{u} r)) : Ideal (strictHenselizationRing v)

def inclusion {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) (K : Set (Index.{u} r)) : AffineSpace {i : Index.{u} r // i ∉ K} S ⟶ V

def fibreIdeal {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) [IsLocalRing (Base r e v)] : Ideal (strictHenselizationRing v)

def PolynomialRing {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) [IsLocalRing (Base r e v)]

def polynomialIdeal {S V : Scheme.{u}} (r : ℕ) (e : V ≅ AffineSpace (Index.{u} r) S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) [IsLocalRing (Base r e v)] (K : Set (Index.{u} r)) : Ideal (PolynomialRing r e v)

structure FibreModels (A B P : CommRingCat.{u}) [IsLocalRing A] (E : Type u) (K : Set E) (I J : Ideal B) (L : Ideal P) (a : A →+* B) (c : A →+* P) (t : E → B) (x : E → P) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (εA : A →+* Ω) (εB : B →+* Ω)
```

The original module publicly imports the new data module. Its public Model and
exists_model signatures are unchanged. The new fibre-comparison lemma imports only
the data module; the original item imports that lemma privately.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCoordinateStrictLocalModel | N4 | Publicly imports the relocated data; same signatures and definitions; the geometric proof uses the new fibre lemma. |
| Sheaf.AlgebraicGeometry.AffineCoordinateStrictLocalFibreComparison | N4 (new) | Uses the shared FibreModels type without importing its parent theorem. |

There are no current direct Lean importers to adapt or compile. DAG parents are not
removed, weakened or withdrawn. No forced adaptation is made.

## Status

landed 20261026T082604-L-2193969 2026-10-26 (merge of deliver/N4/Sheaf.AlgebraicGeometry.AffineCoordinateStrictLocalModel)
