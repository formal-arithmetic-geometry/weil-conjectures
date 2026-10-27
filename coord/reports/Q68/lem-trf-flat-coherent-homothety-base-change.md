## Worker report

The delivery states `DerivedCategory.flat_coherent_homothety_base_change` in
`Sheaf.Algebra.Homology.FlatCoherentHomothetyBaseChange`. Its sole proof is `sorry`.
No definition, new node, dependency repair, or statement correction is needed.

Source read: `literature/stacks-project/more-algebra.tex`, the discussion and displayed
map labelled `equation-base-change-RHom` immediately preceding
`lemma-base-change-RHom`, and case (3) of that lemma (Tag 0A6A). The source defines
the map using extension/restriction adjunction and the normalized internal-Hom
adjunction. The mate of the normalized derived tensorator is the same map: its
uncurried evaluation is tensorator followed by extended evaluation. The module
retains the node's complete four-step proof, including the finite-generator
calculation, pseudo-coherence reduction, scalar-action transposition, and consequences.

Hypotheses and clauses, in order:

- The commutative rings are `{R S : Type u} [CommRing R] [CommRing S]`;
  `[IsNoetherianRing R] [IsNoetherianRing S]` retains both Noetherian hypotheses.
  The specified ring homomorphism and its flatness are `(φ : R →+* S) (hφ : φ.Flat)`.
- `DerivedCategory (ModuleCat.{u} R)` is the ordinary module derived category D(R).
  The existing Grothendieck-category construction supplies its small-Hom localization.
  This uses the ordinary-module presentation already recorded by the two derived
  operation dependencies. Evaluation at the unique object of the bottom-topology
  site identifies its module sheaves with ordinary modules, so this presentation
  covers the node's one-object ringed-site realization without restricting objects.
- The notation D^b_fg is expanded, rather than defined a second time. The premise
  `∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (...obj K)` is exactly vanishing
  outside a finite interval; `∀ i : ℤ, Module.Finite R (...obj K)` is finite generation
  in every degree. The same two premises occur separately for C and Z.
- K_S is `(ModuleCat.ordinaryDerivedExtendScalars φ).obj K`. The first outer
  conjunct quantifies over every bounded finite K and asserts the identical
  boundedness and finiteness conditions for K_S over S.
- RHom is `ordinaryModuleDerivedInternalHom R`, the dependency's abbreviation for
  `Functor.uncurry.obj MonoidalClosed.internalHom`; its object at `(op C, Z)` is
  definitionally `(ihom C).obj Z`. Hence the second outer conjunct's
  `IsIso ((Functor.LaxMonoidal.ihomComparison
  (ModuleCat.ordinaryDerivedExtendScalars φ) C).natTrans.app Z)` says exactly
  that the canonical beta_C,Z is an isomorphism in D(S). The existing comparison
  is the mate of the tensorator, and not an arbitrary chosen arrow. Its source is
  F(RHom_R(C,Z)) and its target is RHom_S(F C,F Z).
- For any L, `MonoidalClosed.id L` is the actual scalar-action arrow. Its definition
  is `curry (ρ_ L).hom`, the transpose of L tensor T -> L under left tensor--Hom
  adjunction. Symmetry identifies this with the node's transpose of
  T tensor L -> L under right tensor--Hom adjunction: both send a scalar to its
  multiplication endomorphism. This uses existing data, without a new homothety.
- The displayed equality is rendered by
  `Functor.LaxMonoidal.ε F ≫ F.map (MonoidalClosed.id C) ≫ beta_C,C =
  MonoidalClosed.id (F.obj C)`, with F written out in the Lean signature.
  The first arrow is S -> F(R), the inverse of the node's canonical F(R) ≅ S
  identification. Its direction makes both sides maps from S, exactly expressing
  equality under that identification. F's unit and tensor structure are the
  normalized ones of the dependency, including its degree-zero counit square.
- The next conjunct is `IsIso (MonoidalClosed.id C) →
  IsIso (MonoidalClosed.id (F.obj C))`, preserving scalar-action invertibility.
- The final conjunct is `IsZero (RHom_R(C,Z)) → IsZero (RHom_S(F C,F Z))`, using
  the dependency's `ordinaryModuleDerivedInternalHom` on both sides.
- No finite projective dimension, finite injective dimension, perfectness,
  faithfulness, or bounds on the derived Hom itself are assumed.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (all ideals finitely generated).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, its localization
  `Q`, and `HasDerivedCategory`; cohomology is `DerivedCategory.homologyFunctor` in
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, defined by finite generation
  of the top submodule.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, defined using flatness via
  the specified ring homomorphism.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the recorded ordinary-module
  presentation of `def-pur-derived-internal-hom`, publicly preserving its generic
  ringed-site construction.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.ordinaryDerivedExtendScalars`, `ordinaryDerivedExtendScalarsMonoidal`,
  and its underlying universal pair `OrdinaryDerivedChangeOfRings` (full signature,
  K-flat counit computation, unit normalization, tensor normalization read).
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`:
  `CategoryTheory.Functor.LaxMonoidal.ihomComparison`, defined by adjunction mate;
  `Mathlib.CategoryTheory.Monoidal.Closed.Basic`: `MonoidalClosed.id`, `ihom.adjunction`.
- Proof imports retain the recorded modules of
  `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion`
  (`DerivedCategory.isPseudoCoherent_iff_boundedAbove_finite_homology`),
  `lem-trf-pseudocoherent-rhom-flat-base-change`
  (`CategoryTheory.exists_pseudoCoherentRHomFlatBaseChange`), and
  `lem-sfb-dc-hom-scalar-adjunction`
  (`CategoryTheory.scalarInternalHomAdjunction_exists`). Their statements and
  docstrings were read. `lem-trf-flat-projective-hom-models` has no Lean record
  or Mathlib match, so there is no module to import for this proof-only dependency.
  Its use is retained in the proof docstring for stage 3.

Edge cases checked before writing: zero rings are allowed by CommRing and flatness;
all conclusions are valid in their zero module categories. Zero K, C, or Z is allowed;
empty cohomological support admits any finite interval (even a > b). The claim does
not require nonzero rings, faithful flatness, or positive length of the support
interval. Identity ring maps give the canonical identity comparison up to the fixed
universal identifications. Finite modules of infinite projective dimension are
allowed because only cohomological bounds and `Module.Finite` occur. Both ring
universes may be embedded in a common arbitrary u; no equality between site object
and morphism universes is imposed. No STATEMENT-DISPUTED issue was found.

Searches for existing notions and statements (2026-10-24):

- `msearch.py ... leanfinder "Flat scalar extension commutes with derived Hom for
  bounded coherent complexes and preserves scalar action"`: 8 hits, on derived
  linearity, Ext, and exact-functor maps. No matching coherent-Hom base-change theorem.
- `msearch.py ... leansearch "Flat base change of bounded coherent complexes
  preserves derived Hom and homothety morphisms"`: 8 hits, including
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` and ordinary flat base-change
  results. None asserts this derived statement.
- `msearch.py ... loogle 'DerivedCategory, "tensor"'`: 0 hits.
- `msearch.py ... grep 'homothety|semidualiz|RHom.*base.change' Algebra/Homology`:
  0 Mathlib hits.
- `rg` in `lean/WeilConjectures` for the item id: no matching module. Searches for
  `homothety`, `semidualiz`, and `ihomComparison` found generic comparison and
  scalar-action tools, particularly the mate definition and
  `Functor.LaxMonoidal.ε_comp_map_id_comp_ihomComparison` in upstream
  `CategoryTheory/Monoidal/Closed/UnitEnd.lean`; these are reused, and they do not
  assert the bounded coherent comparison or preservation conclusions of this item.
- `rg` in `lean/Sheaf` found `SemidualizingRHomConservative` and
  `FiniteMapDualizingTransfer`, which mention homothety for different conclusions;
  it also found the already-recorded ordinary derived operation interfaces. No
  declaration states all the item. No duplicate definition was added.
- Checked `dag/lean_names_upstream.json` for the proposed declaration: no match.

Validation: scompile.py compiled the delivered file separately in sandbox mode
(17.5 seconds) and its actual library module mode (7.5 seconds), with no errors or
warnings. Module mode, explicit universe/variables, public statement imports,
private proof imports, and the 100-character line limit are respected.

## Second reading by Q68

Author's second reading, with the node and final Lean file reopened; the maintainer
performs the independent review, as required by the dispatcher brief. No subagent
was started.

I checked both Noetherian rings and the specific flat map against the binders,
then checked that the first outer conjunct covers every K separately from C and Z.
The two bounds and all-degree finiteness hypotheses for C and Z are retained
individually. The second outer conjunct has four conclusions: beta_C,Z invertible,
the homothety equality using beta_C,C, preservation of homothety invertibility,
and preservation of Hom vanishing. I checked the Hom endpoints against the
recorded abbreviation and the mate definition, and checked the unit-map direction:
ε goes from S to F(R), so the displayed equation is exactly the node's equality
under F(R) ≅ S. The right-unitor transpose is the symmetry-equivalent scalar action
of the left-unitor wording in the node. The zero object uses categorical IsZero,
not an invalid IsZero on a bare Type. There are no hidden let binders, arbitrary
comparison choices, projective/injective dimension hypotheses, or proved lemmas.
No mismatch requiring a change was found. The node copy changes only `lean`.
