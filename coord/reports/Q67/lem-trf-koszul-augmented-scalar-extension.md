## Worker report

The delivery states `ExteriorAlgebra.KoszulAugmentedScalarExtension.exists_augmented_scalar_extension`
in `Sheaf.RingTheory.KoszulAugmentedScalarExtension`. Its only postponed proof is this theorem.
The eight helper declarations contain actual data: abbreviations of the given Koszul complex and
quotient, the specified mixed total tensor, and compositions of existing canonical isomorphisms.
There is no choice from an unproved existence result and no new independent mathematical notion.
The node changes only in `lean`; no statement correction or dependency repair is needed.

Source read: `literature/stacks-project/more-algebra.tex`, label
`lemma-koszul-regular-flat-base-change` (Tag 062H), especially its first complex identity;
the given definition node and `WeilConjectures.AlgebraicGeometry.KoszulComplex` for Tags 0622/0623.
Flatness in the surrounding 062H lemma is needed for its homology/regularity assertions, not for
this identity of complexes. The balanced quotient and augmentation calculations are the explicit
calculations in the accepted six-step proof of this item.

Hypothesis and clause correspondence:

- Commutative rings and arbitrary ring homomorphism: `{A S : Type u} [CommRing A]
  [CommRing S] (φ : A →+* S)`. There is no flatness, regularity, nontriviality, or proper-ideal
  hypothesis. A common arbitrary universe accommodates both rings; `w` is an independently chosen
  morphism universe for the output derived category.
- Length and arbitrary sequence: `(r : ℕ) (g : Fin r → A)`, including `r = 0`.
- Ideals `I` and `I_S`: `Ideal.span (Set.range g)` and
  `Ideal.span (Set.range (φ ∘ g))`, respectively, in `quotient`.
- The exact Koszul complexes in cochain degrees `-q`: `complex R g` is precisely
  `(ExteriorAlgebra.koszulComplex R r g).extend ComplexShape.embeddingDownNat`.
  `degreeIso` is the existing `HomologicalComplex.extendXIso`, not another construction of Koszul.
- Quotient augmentations: the theorem provides `εA : complex A g ⟶ quotientComplex A g` and
  `εS : complex S (φ ∘ g) ⟶ quotientComplex S (φ ∘ g)`. The following two equalities identify
  their degree-zero components, after the canonical single-object identification, with
  `quotientComponent`. This component is the degree-zero exterior-power identification followed
  by `I.mkQ`. Every other component has zero target because `quotientComplex` is a single in
  degree zero. Thus these are the unique specified quotient augmentations; their existence is
  part of the conclusion, not an added assumption about arbitrary maps.
- `F(E) = Tot(E ⊗_A S[0])` with its `S`-action: `total φ` uses exactly
  `ModuleCat.mixedTotalTensor φ`, evaluated at `S[0]` in its first slot. The dependency's native
  convention is scalar-first order, so its elements `s ⊗ x` represent the statement's `x ⊗ s`
  under the canonical factor flip. Since this factor has degree zero, the flip contributes no
  Koszul sign. The differential is `1 ⊗ d_E`.
- Localization `Q_S`: `[HasDerivedCategory.{w} (ModuleCat.{u} S)]` and `DerivedCategory.Q`.
- Balanced quotient isomorphism `θ`: an isomorphism in `ModuleCat S` from
  `(ModuleCat.extendScalars φ).obj (quotient A g)` to `quotient S (φ ∘ g)`. The first formula
  is `θ.hom (s ⊗ₜ[A, φ] mk a) = mk (φ a * s)` for every `a,s`. With the explicit flip just
  described this is exactly `ā ⊗ s ↦ class(φ(a)s)`. The second formula specifies the inverse,
  `θ.inv (mk s) = s ⊗ₜ[A, φ] 1`, hence `class(s) ↦ 1̄ ⊗ s` in the source order.
  These formulas specify the canonical isomorphism, not an unconstrained invertible map.
- The representing cochain isomorphism: `b : (total φ).obj (complex A g) ≅ complex S (φ ∘ g)`.
  For every `q`, tuple `i : Fin q → Fin r`, and coefficient `s`, the wedge formula specifies its
  component on the pure tensor of the standard wedge. `totalDegreeIso` removes the mixed
  tensor's extra unit and degree-zero totalization; `degreeIso` changes only the index from
  chain degree `q` to cochain degree `-q`. The output is exactly `s` times the corresponding
  wedge over `S`. Allowing all tuples is equivalent to specifying the ordered basis wedges:
  permutations change both sides by the same alternating sign and repetitions give zero.
  For `q=0`, `exteriorPower.ιMulti` is the empty wedge and this is the tensor unit map.
- The derived isomorphism `β`: its endpoints are precisely `Q_S F(K_A(g))` and `Q_S K_S(φg)`;
  the equality `β = DerivedCategory.Q.mapIso b` records its prescribed representative.
- Canonical identification of `F((A/I)[0])`: `totalSingleIso φ (quotient A g)` is built from
  `CochainComplex.mapBifunctorSingle₁Iso`, `HomologicalComplex.singleMapHomologicalComplex`, and
  the module tensor left unitor. Its target is the single of the scalar-extended quotient.
- The square: the final equation is `Q.map (F.map εA)` followed by `Q.map totalSingleIso.hom`
  and `Q.map (singleFunctor.map θ.hom)`, equal to `β.hom ≫ Q.map εS`. With Lean's left-to-right
  composition and the displayed canonical single identification this is precisely
  `Q_S(θ[0]) ∘ Q_S(F(εA)) = Q_S(εS) ∘ β`.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.KoszulComplex`: `ExteriorAlgebra.koszulComplex`, with
  `koszulBoundary` defined by restriction of `CliffordAlgebra.contractLeft` and its full docstring.
- `WeilConjectures.Algebra.Homology.MixedTotalTensor`: `ModuleCat.mixedTensor` and
  `ModuleCat.mixedTotalTensor`, including the full curried signatures and the two coefficient rings.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, and the localization interface.
- Proof dependency `lem-weil-pbc-tensor-quotient-base-change`: its exact Mathlib match
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` and its two pure-element formulas, read
  in `Mathlib/RingTheory/TensorProduct/Quotient.lean:52,64,69` and imported for stage 3.
- Proof dependency `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`, its bilinearity
  relations, `TensorProduct.lift`, `TensorProduct.ext'`, and `LinearMap.rTensor` with its pure-tensor
  formula, read in the recorded Defs/Basic/Map sources. They are available through the mixed tensor.
- Proof dependency `lem-weil-pbc-exterior-power-free-basis`: its Mathlib matches
  `Module.Basis.exteriorPower`, `exteriorPower.coe_basis`, `zeroEquiv`, and `oneEquiv`, read with
  signatures and docstrings in ExteriorPower/Basis.lean and Basic.lean. The basis module is a
  non-public proof import; the component normalization uses `ιMulti` and `zeroEquiv`.
- Canonical-interface helpers use `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`
  (`mapBifunctorSingle₁Iso`), Mathlib's `singleMapHomologicalComplex`, `singleObjXSelf`, and
  `Embedding.Extend` (`extendXIso`). They implement the unit identifications in the node.

Edge cases checked mathematically before drafting and again against the signature:

- `r=0`: ideals are zero, only degree zero survives, and the empty wedge gives the unit map.
- Zero source or target rings: no `Nontrivial` instance is required, and the tensor/quotient formulas
  remain valid on zero modules. The isomorphism carries no assumption that basis vectors are nonzero.
- Non-flat `ℤ → ℤ/2`, with sequence `(2)`: the resulting Koszul differential over the target is zero,
  but the comparison is still an isomorphism of the actual complexes, not a claimed resolution.
- Sequence containing `1`: both quotients are zero, so the augmentation square remains meaningful.
- `q>r`: all standard wedges vanish; the tensor and target exterior powers are zero.
- Characteristic two: the same alternating differential and wedge maps apply; no division or sign
  nonvanishing is assumed.

Searches actually run:

1. `msearch.py ... leanfinder "The augmented Koszul complex commutes with arbitrary extension of
   scalars and its quotient augmentation square commutes"`: eight cotangent base-change hits;
   none states the augmented Koszul result or the normalized square.
2. `msearch.py ... loogle "Algebra.TensorProduct.quotIdealMapEquivTensorQuot"`: three hits, the
   quotient tensor equivalence and its two pure-element formulas; these supply only the quotient
   ingredient, already represented by the proof-dependency node.
3. `msearch.py ... grep "koszul.*[Bb]ase|koszul.*[Aa]ugment|quotIdealMapEquivTensorQuot"`:
   eleven hits, all using or defining the quotient equivalence, no whole-statement match.
4. `msearch.py ... leansearch "Koszul complex base change quotient augmentation commuting square"`:
   eight hits on cotangent comparisons and unrelated complex squares, no exact statement.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for Koszul scalar/base change,
   augmentation, cochain and wedge names; direct node-id search in `lean/WeilConjectures` and
   `dag/lean_names_upstream.json`: no declaration of this item. Read the full upstream
   `WeilConjectures.RingTheory.KoszulBaseChangeIso` theorem and private construction: its public
   theorem only asserts `Nonempty` of a chain isomorphism, with neither normalization nor square.
   It therefore cannot be an `existing: true` match. Read the parent module
   `Sheaf.RingTheory.KoszulDerivedQuotient`: its ordinary quotient comparison is for the particular
   polynomial zero-section and its theorem assumes Koszul regularity, so it is not this statement.
6. Additional searches for quotient augmentations located the regular-sequence projective-resolution
   statements, a private power augmentation, and the shifted-tail augmentation. Their full signatures
   were read; none gives a public arbitrary-sequence augmented scalar-extension theorem. The new
   statement specifies its augmentations existentially by their unique quotient component instead of
   importing an inapplicable regularity assumption or an arbitrary map.

Validation: the prescribed `scompile.py` compiled the sandbox and library module cleanly (2.7 s
and 2.6 s), with no errors or disallowed warnings. `autoImplicit false` is enabled. All declarations
and universes are explicitly bound, every line is at most 100 columns, and there is exactly one
`sorry`, the main theorem. No statement is disputed.

## Second reading by Q67

This dispatcher brief assigns one worker and forbids starting other agents. The following is a
final self-check; it does not claim independent authorship. The maintainer's delivery review supplies
the independent reading specified by this assignment.

Re-read the unchanged node and the delivered signature. Checked every binder and clause against
the correspondence above, particularly: the absence of flatness/regularity; the native scalar-first
mixed tensor and its tensor unit; both directions of the quotient comparison; exact degree-zero
normalization of both augmentations; all wedge degrees including zero; `β = Q.mapIso b`; and the
order and endpoints of all three maps on the left of the square. The existential augmentation maps
are uniquely fixed by the displayed components, so their use introduces no arbitrary map hypothesis.
The helper definitions contain only canonical existing constructions. No mismatch or statement
change was found. No new definition nodes or dependency modules are delivered.
