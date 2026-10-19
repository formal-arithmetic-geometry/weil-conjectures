## Worker report

The delivery states `AlgebraicGeometry.Etale.geometricPoint_projection_comparison`
in `Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison`. Its sole postponed
proof is this theorem. Every definition has its actual construction. The DAG's
statement is unchanged.

The theorem specializes the transparent predicate `GeometricPointProjectionSquare`.
That predicate spells out the equality of the two paths and universally quantifies
`E : C` and `M : D`. It does not assume that the square commutes. Writing the
formula before specializing the categories avoids the kernel's expensive reduction
of derived tensor localization objects in the saved specialized map definitions.
This is one module, with no raised compilation limit and no opaque replacement of
a canonical construction.

Hypothesis and clause correspondence:

- The algebraically closed field is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`.
  The arbitrary scheme and morphism are `{Z : Scheme.{u}}` and
  `(h : Z ⟶ Spec (.of Ω))`. There are no further geometric assumptions.
- Integer coefficients use `GeometricPointIntegerModule`, an abbreviation for
  `ModuleCat.{u + 1} (ULift.{u + 1} ℤ)`. This is the dependency's fixed encoding of
  ordinary abelian groups; it introduces no new coefficient construction.
- In the predicate, `C`, `A`, and `D` specialize respectively to the unbounded
  derived categories of integer sheaves on `Z`, integer sheaves on `Spec Ω`, and
  integer modules. `∀ (E : C) (M : D)` includes every unbounded object. Tensor
  products are the existing monoidal derived tensors, the `curriedTensor` used by
  `Etale.derivedTensor`, with no completion, boundedness or torsion condition.
- The predicate's `F,H` are the recorded derived inverse and direct image;
  `S,K` are `(geometricPointStalk Ω).mapDerivedCategory` and
  `(geometricPointConstants Ω).mapDerivedCategory`. The registered monoidal stalk
  is precisely the projection of `nonempty_geometricPointDerivedConstantsData`.
- `L,R` are the left derived constant-sheaf functor on `Z` and the existing
  `rightDerivedGlobalSections`. The exact-functor identifications normalize
  left-derived inverse image and constants to the dependency's termwise functors.
- `β` is exactly `geometricPointDerivedSectionsIso Ω h`, whose dependency theorem
  supplies its counit and degree-zero normalizations. It is not an arbitrary iso.
- `γ` is `geometricPointProjectionCoefficientIso Ω h`: whisker the canonical
  left-derived/exact comparison for inverse image, compose with
  `geometricPointSectionsConstantsIso Ω h`, then with inverse to the canonical
  left-derived/exact comparison for constants on `Z`. Thus its component is exactly
  the specified coefficient comparison, in the horizontal maps' normalization.
- `unit` is the unit of
  `(geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction`.
  Its invertibility is the corresponding projection of the normalized equivalence
  data, using the same chosen adjunction as the dependency.
- The upper horizontal `P` is exactly `rightDerivedLowerStarProjectionMap`.
  The predicate applies it at `E` and `K.obj M`, then applies `S.map`.
- The lower horizontal `p` is exactly the natural transformation evaluated by
  `constantDerivedProjectionMap`: the `rightAdjointProjectionMap` of
  `derivedConstantGlobalSectionsAdjunction` with the recorded
  `leftDerivedTensorComparison`. Reading that dependency's definition confirms
  that `(p.app E).app M` is its recorded projection morphism, not a replacement.
- The right vertical arrow is `β.hom.app (E ⊗ F.obj (K.obj M))` followed by
  `R.map (E ◁ γ.hom.app M)`, exactly the node's delta.
- The left vertical arrow is `Functor.OplaxMonoidal.δ S (H.obj E) (K.obj M)`,
  then `S.obj (H.obj E) ◁ inv (unit.app M)`, then `β.hom.app E ▷ M`.
  This is the node's alpha. Tensor functoriality identifies doing the unit inverse
  before beta with the stated order of the two independent tensor factors.
- The equality is top-then-right equals left-then-bottom. It neither inverts nor
  asserts invertibility of a horizontal morphism.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants`:
  `geometricPointConstants`, `geometricPointStalk`,
  `GeometricPointDerivedConstantsData`,
  `nonempty_geometricPointDerivedConstantsData` and its normalized monoidal/unit
  fields.
- `Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction`:
  `geometricPointSectionsStalkAdjunction`,
  `geometricPointSectionsConstantsIso`, `geometricPointDerivedSectionsIso`, and
  `geometricPoint_derivedSections_adjunction` for the canonical normalizations.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `rightDerivedLowerStarProjectionMap` and its full signature and adjunct formula.
- `Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap`:
  `derivedConstantGlobalSectionsAdjunction`, `constantDerivedProjectionMap`, and
  the normalized constant-sheaf monoidal and flat-preservation instances.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`: `derivedTensor`, whose body
  is `curriedTensor` of the existing derived monoidal category.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and Mathlib
  `Algebra.Homology.DerivedCategory.Basic`: the existing module-derived categories
  and `DerivedCategory`. The dependency encoding is retained.
- `Sheaf.Paper.RingedProjectionTensorComposition` is imported for the node's stated
  proof dependency; its existing composition theorem is the planned proof input.

The source was checked in local Stacks `sites-cohomology.tex` at
`equation-projection-formula-map` (the counit-defined map without further
assumptions), and `etale-cohomology.tex` at `lemma-projection-formula-proper`
(the final geometric-fibre formula). The main docstring carries the node's four
proof steps, including the canonical counit comparison and composition identity.

Edge cases checked: the empty scheme, zero objects, the identity morphism over the
point, arbitrarily shifted/unbounded objects, and every characteristic of Ω are
all permitted. The generic formula has independent object and morphism universes
for its three categories. Its specialization retains the dependencies' coefficient
and site universes. There are no extra equality or finiteness hypotheses.

Searches for existing declarations:

- Saved searches in the node include LeanSearch on comparison of derived direct
  image tensor projection with constant-coefficient derived sections (8 related
  categorical results), LeanFinder on monoidal transport/counit compatibility
  (8 generic coherence results), Loogle on projection/counit names (0 hits), and
  grep of Mathlib's category-theory files (no matching theorem).
- Repeated through `msearch.py`: LeanFinder query "Derived projection map compatible
  with geometric stalk constant sheaf equivalence" returned 8 structure-sheaf/germ
  results, none about the derived projection square; Loogle query
  `"rightDerivedLowerStarProjectionMap"` returned 0; grep query
  `projection.*[Cc]omparison` in Mathlib/CategoryTheory returned 0.
- `rg` on the item id and `geometricPoint_projection_comparison` in upstream
  `WeilConjectures` and the shared `lean/Sheaf` found no existing declaration.
  The dependency maps and generic projection machinery exist and are reused.

No statement dispute, DAG correction, new node or dependency module is needed.

## Second reading by NQ

A separate self-check pass reread the node, source signatures and final module.
The saved packet had the left map's source at the upper-right corner instead of
`S(Rh_* E ⊗ C_s M)`, and introduced an unnecessary `eqToHom (by rfl)` in the right
map. The repair removes those specialized definitions and writes the whole
commuting-square formula in `GeometricPointProjectionSquare`; the theorem fixes
every map argument to the recorded canonical construction. No arbitrary map or
additional compatibility assumption is quantified in the specialized theorem.

The check matched the arbitrary Ω/Z/h and E/M clauses, ordinary integer tensors,
the direction and normalization of both vertical arrows, and both counit-defined
horizontal arrows. The explicit `γ` transport uses the forward inverse-image
comparison and inverse constant comparison, so its direction is unchanged.
The inverse germ is used only in alpha. The literal predicate equality has the
correct common source and target. The lower natural transformation is the exact
one in `constantDerivedProjectionMap`'s defining expression. Definitions remain
transparent and contain no postponed data. Only the theorem's proof is `sorry`.

This dispatcher brief prohibits starting another agent; this section records the
required self-check, not an assertion that another worker was launched. The
maintainer's independent mathematical review remains the delivery review.

## Repair and validation

The required initial `deliver2.py --no-push` reproduced the saved 60-second timeout
locally and on server confirmation. Prefix checks isolated the expensive
specialized comparison definitions. Making the dependency comparisons opaque did
not resolve it and is not included in the delivery. The repaired categorical
formula is in the same item module and preserves the complete square.

The prototype of the repaired formula compiled with no errors or warnings in
7.5 seconds (sandbox) and 4.9 seconds (module) under `scompile.py`'s unchanged
60-second limit. The final module, including its complete documentation and proof import, compiled
cleanly in 5.5 seconds (sandbox) and 4.9 seconds (module). The first repaired
packet dry run found only that the stored signature included the `:=` delimiter;
this was removed to match the preflight signature convention. The mandatory dry
run is repeated on that repaired record before delivery.
