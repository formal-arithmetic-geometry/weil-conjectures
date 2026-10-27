## Worker report

The new module `Sheaf.AlgebraicGeometry.FlatModulePresentationAfterBoundaryBlowup`
states `AlgebraicGeometry.Scheme.Modules.flatModulePresentationAfterBoundaryBlowup`.
Its sole theorem has proof `sorry`; there are no new definitions, auxiliary theorems,
new nodes, dependency repairs, or statement corrections. The item's original statement,
proof and dependency lists are unchanged.

Sources read: Stacks `flat.tex`, lemma
`lemma-flat-finite-type-finitely-presented-over-dense-open` (081N), the third paragraph
of `remark-successive-blowups` (080Y), and the final paragraph of
`theorem-flatten-module` (0815). The current blueprint ancestor's proof was also read
at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`.
The item's four proof steps are carried into the theorem's docstring.

Hypotheses and conclusions, clause by clause:

- The schemes are `{X S : Scheme.{u}}`; `[CompactSpace S] [QuasiSeparatedSpace S]`
  mean exactly that the base is qcqs. No compactness or separation assumption is
  imposed on X.
- The map is `(f : X ⟶ S)` with `[LocallyOfFinitePresentation f]`, Mathlib's affine-local
  finite-presentation predicate.
- The module is `(F : X.Modules)`, with `[hF : F.IsQuasicoherent] [F.IsFiniteType]`.
  These are the two Mathlib predicates also exposed by the recorded
  `CoherentFiniteType` dependency; no coherence hypothesis is imposed.
- Relative flatness is `(hflat : F.IsFlatOver f)`, the recorded affine-sections
  predicate, equivalent to stalk flatness for this quasi-coherent F.
- The open is `(U : S.Opens)` with `(hU : IsCompact (U : Set S))`.
- Finite presentation over U is
  `((restrictFunctor (f ⁻¹ᵁ U).ι).obj F).IsFinitePresentation`.
  This is precisely restriction to X_U, not finite presentation over U itself.
- The initial existential gives `I : S.IdealSheafData` with
  `I.toModules.IsFiniteType` and `(I.support : Set S) = (U : Set S)ᶜ`.
  IdealSheafData already encodes a quasi-coherent ideal; `support` here is V(I).
- The remainder is universally quantified over every such I and every proof
  `hI : I.toModules.IsFiniteType`, assuming exactly the same support equality.
  It does not merely establish the properties for a specially chosen centre.
- The blowup and its map are the recorded `I.blowup` and `I.blowupMap`.
  `∃ B : IsAdmissible S U, B.I = I` expresses admissibility while retaining this
  exact centre. For the canonical blowup the identification with itself is the
  identity; no arbitrary isomorphic blowup replaces it.
- `CompactSpace I.blowup ∧ QuasiSeparatedSpace I.blowup` gives the qcqs new base.
- `IsCompact` of the underlying set of `I.blowupMap ⁻¹ᵁ U` is quasi-compactness
  of U_T. `IsRetrocompact` of that same set means its intersection with every
  compact open is compact, exactly the parenthetical definition in the node.
- `IsSchemeTheoreticallyDominant (I.blowupMap ⁻¹ᵁ U).ι` gives schematic density.
  Mathlib defines this by the vanishing of the kernel ideal. For this
  quasi-compact open immersion (retrocompactness is already a conclusion), it
  is equivalent to injectivity of O_T → j_* O_{U_T}, as required. This uses
  Mathlib's existing density notion, not a new definition.
- `IsIso (cokernel.π (kernel.ι (moduleStrictTransformRestriction f I F)))`
  asserts that the actual canonical quotient from p*F to its strict transform
  is an isomorphism. Its source is `(tensorPullback (pullback.fst f I.blowupMap)).obj F`
  and its target is definitionally `@moduleStrictTransform _ _ f I hI F hF`.
  Thus the canonical identification is fixed, rather than an arbitrary
  existence of an isomorphism. The same expression is the body of the existing
  `moduleStrictTransformQuotient` in the proof dependency; no duplicate helper
  is introduced or exported here.
- The last two conjuncts say that this strict transform is `IsFlatOver`
  `pullback.snd f I.blowupMap` and is `IsFinitePresentation` on the whole
  `pullback f I.blowupMap`. No restriction to a smaller open appears in this
  conclusion. Through the canonical quotient isomorphism these are also
  properties of the ordinary pullback p*F.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `WeilConjectures.Blowup.Gluing` (publicly through AdmissibleBlowup and
  ModuleStrictTransform): `Scheme.IdealSheafData.blowup` and `blowupMap`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` publicly imports
  the explicit `Scheme.Modules.tensorPullback` construction from
  `WeilConjectures.AlgebraicGeometry.TensorPullback`; its recorded normalized
  adjunction is available, while the statement uses the tensor construction
  through the strict-transform restriction map.
- `def-weil-pbc-scheme-conventions` is explicitly a convention-only node, with
  no own declaration; the standard Scheme, CompactSpace and morphism
  properties are used directly.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated` and the equivalent scheme condition
  `QuasiSeparatedSpace`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  the recorded public `SheafOfModules.IsQuasicoherent` and
  `SheafOfModules.IsFiniteType`, also packaged by its
  `Scheme.Modules.IsQuasiCoherentFiniteType` conjunction.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators` and `Quasicoherent`
  (public through CoherentFiniteType): `SheafOfModules.IsFiniteType` and
  `SheafOfModules.IsFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`.
- `WeilConjectures.Blowup.AdmissibleBlowup`: `AlgebraicGeometry.IsAdmissible`.
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform`:
  `Scheme.Modules.moduleStrictTransformRestriction`, `moduleStrictTransform`.

Additional standard notions are Mathlib `IsRetrocompact`, and
`IsSchemeTheoreticallyDominant`; both definitions and the latter's
`Scheme.Hom.app_injective` interface were inspected. These notions already
exist and do not require a definition node.

The stated proof dependencies are imported without `public`:
`NagataBoundaryDivisorCartier`, `FlatFiniteTypeDensePresentation`, and
`ModuleAdmissibleBlowupCalculus`. The two admissible-blowup proof dependencies
are in the already public `WeilConjectures.Blowup.AdmissibleBlowup`.
The qcqs permanence dependency is a Mathlib leaf: its individual compactness,
quasi-separatedness and base-change results are supplied by the existing
morphism imports. No unstated prerequisite or import cycle was encountered.

Edge cases checked against the sources:

- U = S: V(I) is empty, the ideal is the unit ideal, and the blowup is the
  identity. The finite-presentation hypothesis is already global.
- U = empty: V(I) is the entire base. For a finite-type ideal this makes it
  locally nilpotent, so the blowup is empty; the density and module assertions
  are then vacuous on the empty scheme. No nonempty-open hypothesis is added.
- Empty S or X, and the zero module, are permitted. All sheaf predicates are
  meaningful in these cases and no rank or nonzero-section condition occurs.
- Non-Noetherian S and non-quasi-compact X are retained. The 081N criterion
  is local on X and S, as its proof explicitly states.
- The same arbitrary universe u is used for the schemes and their modules;
  there is no quantification over test schemes in an independent smaller
  universe and no artificial equality of site universes.

Searches actually run with `batch2/msearch.py` for Q123 and this item:

- LeanFinder, `Flat finite type module becomes finitely presented after blowup
  of complement of quasi compact open`: 8 hits. They concern finite-presentation
  ring localizations, the locally-finite-presentation class, affine ring-map
  signatures, and the factorization criterion for flat modules. None is this
  boundary-blowup theorem.
- LeanSearch, `Flat finite type quasicoherent module is finitely presented after
  boundary blowup`: 8 hits. `Module.finitePresentation_of_finite` requires a
  Noetherian ring, absent here; the other hits give finite presentations from
  existing finite presentations or their data, not from a boundary blowup.
- Loogle, `"IsFinitePresentation", "Flat"`: 0 hits.
- Mathlib grep, `blowup|strictTransform|[Ss]chematically[Dd]ense`, restricted to
  AlgebraicGeometry: 0 hits.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `boundary[Bb]lowup|flat_module_presentation_after|flatModulePresentationAfter|presentation_after_boundary|lem-trf-flat-module-presentation-after-boundary-blowup`:
  no existing declaration or occurrence. A broader search for flatness and
  presentation identified the dense-open criterion and the strict-transform
  calculus; these are the existing proof dependencies and were read in full.
- The prescribed grep for the item's id in `lean/WeilConjectures` returned no
  occurrence. No existing full-statement match was found.

Validation: `scompile.py Q123 lem-trf-flat-module-presentation-after-boundary-blowup`
compiled the delivered file in both sandbox and library modes, successfully,
with no reported warnings or errors. All variables are explicit and both
implicit-variable options are disabled. No STATEMENT-DISPUTED or node fault.

## Second reading by Q123

This is a second self-reading, not an independent worker review: the dispatcher
explicitly prohibits starting another agent, and the maintainer supplies the
independent review after delivery. With the node and module open, I checked
that each hypothesis and clause is represented in the correspondence above.
In particular the universal quantification over arbitrary boundary ideals,
centre equality in admissibility, canonical quotient rather than an arbitrary
isomorphism, explicit retrocompactness, and finite presentation on the entire
fibre product match the node. The only compactness hypotheses are those on S
and U. The quotient is exactly the cokernel defining the recorded strict
transform, with explicit finite-type and quasi-coherence proof arguments.
No mismatch or statement correction was found. No extra modules or nodes
were needed.
