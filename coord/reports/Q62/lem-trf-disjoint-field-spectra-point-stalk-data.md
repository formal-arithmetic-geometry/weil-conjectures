## Worker report

The module `Sheaf.AlgebraicGeometry.DisjointFieldSpectraPointStalkData` states
`AlgebraicGeometry.disjoint_field_spectra_point_stalk_data`, with its sole proof `sorry`.
Three fully constructed helpers in the same owning module name the specified point,
coordinate-section map and germ map. They introduce no independent notion and select
no data from an unproved existence theorem. The node changes only in `lean`.

Source read: Stacks `morphisms.tex`, Tag 02G7, `lemma-unramified-over-field`, part (1)
and its proof, especially the discrete-space/local-ring description. Also read the
Mathlib stalk/germ colimit interface corresponding to `sheaves.tex`, Tag 0078.
The assertion extracts point and local-ring identifications; it does not import the
finite separability assumptions from the unramified characterization.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`.
- A scheme Y over k: `(Y : Scheme.{u}) (f : Y ⟶ Spec (.of k))`. A structure morphism
  is the data of `Scheme.Over`; no extra property of f is assumed.
- Any index set: `(I : Type v)`, with v independent of u. There is no `Finite`,
  `Fintype`, `Nonempty` or `Small` assumption.
- Open subschemes: `(U : I → Y.Opens)`, using Mathlib's canonical `(U i).toScheme`
  and inclusion `(U i).ι`.
- Pairwise disjoint: `hdisjoint : Pairwise (fun i j ↦ Disjoint (U i) (U j))`.
- Cover Y: `hcover : iSup U = ⊤`.
- Field extensions: `(L : I → Type u) [∀ i, Field (L i)] [∀ i, Algebra k (L i)]`.
  Neither module finiteness nor separability nor algebraicity appears.
- Specified k-isomorphisms: `e : ∀ i, (U i).toScheme ≅ Spec (.of (L i))`, and `hover`
  says its composite to Spec k is `(U i).ι ≫ f`, with the structure map of Spec L
  given by `Spec.map (CommRingCat.ofHom (algebraMap k (L i)))`.
- The point y_i is `fieldSpectrumOpenPoint (e i)`, defined as the image under
  `(e i).inv` of `IsLocalRing.closedPoint (L i)`. It belongs to U_i by its subtype
  and is the unique point because Spec of a field has exactly one prime.
  `.val` regards it as a point of Y.
- Bijection of I with Y is exactly `Function.Bijective (fun i ↦ ... .val)`.
- Every point y_i is closed: `... .val ∈ closedPoints Y`, definitionally the
  closedness of its singleton.
- The section identification L_i → Γ(Y,U_i) is `fieldSpectrumOpenSections (e i)`:
  `(Scheme.ΓSpecIso (.of (L i))).inv ≫ (e i).hom.appTop ≫ (U i).topIso.hom`.
  All three factors are canonical isomorphisms. The direction follows the
  contravariance of sections for e_i : U_i ≅ Spec L_i.
- The actual germ map L_i → O_(Y,y_i) is `fieldSpectrumOpenGerm (e i)`, the above
  section map followed by `Y.presheaf.germ (U i) y_i y_i.property`.
  `IsIso (fieldSpectrumOpenGerm (e i))` asserts its invertibility as a ring map.
- The immediately following scalar equation identifies its composite with
  `algebraMap k (L i)` with the canonical k → O_(Y,y_i), explicitly
  `(Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.presheaf.germ ⊤ y_i trivial`.
  Thus the invertible ring map is an isomorphism of k-algebras with the structure
  induced by f. This is the unbundled equivalent of an `AlgEquiv`, not merely an
  unspecified ring isomorphism or an arbitrary algebra structure.
- The composite with the canonical residue quotient is explicitly
  `fieldSpectrumOpenGerm (e i) ≫ Y.residue y_i`. Its `IsIso` and following scalar
  equation express that this same composite is a k-algebra isomorphism. The scalar
  map to κ(y_i) is exactly the preceding structure-to-stalk map followed by
  `Y.residue y_i`, as required by the quotient algebra structure.
- The final `IsIso (Y.residue y_i)` is the asserted canonical residue quotient
  itself. Its k-linearity is built into that quotient algebra structure; no
  alternative quotient or arbitrary identification of the residue field is used.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `AlgebraicGeometry.Spec`, `Spec.map`, `Scheme.ΓSpecIso`, `Scheme.Hom.appTop`.
- `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over` and `Scheme.Hom.IsOver`; the theorem
  uses their explicit structure morphism and commuting-triangle presentation.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap` for field extensions.
- `Mathlib.Topology.JacobsonSpace`: `closedPoints`, `mem_closedPoints_iff`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  and `Scheme.Hom.residueFieldMap`; the quotient in the statement is `Scheme.residue`.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `ι`, `topIso`;
  also inspected `stalkIso` and its germ compatibility, without making a copy.
- Proof-only imports follow the recorded dependency declarations:
  `Mathlib.AlgebraicGeometry.OpenImmersion` (`IsOpenImmersion`),
  `WeilConjectures.Topology.PresheafModuleStalkFunctor`
  (`PresheafOfModules.moduleStalkFunctor`, whose carrier is the existing stalk), and
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (`LocallyRingedSpace.Hom`).
  These remain private proof imports, as the stage-2 contract requires.

Edge cases checked mathematically before writing: empty I forces empty Y by the
cover, and the pointwise conclusions are vacuous; no default element of I is used.
A nonempty piece is forced by its isomorphism with a field spectrum. An infinite
partition has open singleton complements by arbitrary unions, so no quasi-compactness
or finite-union assumption is needed. Purely inseparable and transcendental L_i/k
are allowed. The scalar maps come from f and hover, so a nontrivial field automorphism
in e_i changes the named canonical field-to-stalk map as it should. A single summand
recovers the usual field-spectrum stalk and residue quotient. Scheme, base and field
universes share a common ambient u to form their scheme morphisms; the index has
its own universe v, with no cardinal bound imposed.

Searches actually run with `msearch.py Q62 lem-trf-disjoint-field-spectra-point-stalk-data`:

- `leanfinder`: “An open partition of a scheme by spectra of fields identifies its
  points stalks and residue fields with those fields”: 8 hits, including
  `Scheme.SpecToEquivOfField`, `Scheme.SpecMap_residue_apply` and field-spectrum point
  instances; none states the partition bijection, closedness and canonical algebra
  isomorphisms together.
- `loogle`: `AlgebraicGeometry.Scheme.Opens.stalkIso, AlgebraicGeometry.Scheme.residue`:
  service succeeded, zero hits for the combined query.
- `grep`: `stalk.*(Field|field)|[Ff]ield.*stalk|stalkIso`, subdirectory
  `AlgebraicGeometry`: 25 hits, including `Scheme.Opens.stalkIso` and projective-spectrum
  stalk maps; no matching theorem.
- `leansearch`: “For a scheme partitioned by open spectra of fields the germ and
  residue quotient are algebra isomorphisms”: 8 hits, including
  `StructureSheaf.germ_toOpen`, `Scheme.Opens.germ_stalkIso_hom_assoc`, `Scheme.residue`,
  and `ΓSpecIso_hom_stalkClosedPointIso_inv`; these are components, not this theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `disjoint.*[Ff]ield|[Ff]ield.*[Pp]artition|lem-trf-disjoint-field-spectra-point-stalk-data`
  found field decomposition, finite-support and finite-product statements, with no
  arbitrary open partition point/stalk result. In particular
  `UnramifiedFieldFibreDecomposition.lean` has a finite-separable decomposition
  characterization, not this assertion; its full statement was read.
- `grep -rn` for the exact item id in `lean/WeilConjectures` had no hit. `rg` for all
  four proposed declaration names in Mathlib, `WeilConjectures`, `Sheaf` and
  `dag/lean_names_upstream.json` had no hit. Additional direct searches inspected
  canonical section, stalk and residue scalar APIs in those sources.

No statement correction, dependency repair, new node or disputed statement is needed.
The supplied scompile.py compiled the module cleanly in both sandbox and library mode
(3.2 and 1.9 seconds respectively); the sole postponed theorem belongs to this node.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
