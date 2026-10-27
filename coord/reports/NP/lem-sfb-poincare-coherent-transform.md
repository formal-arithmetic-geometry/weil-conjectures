## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.PoincareCoherentTransform` states
`AlgebraicGeometry.IsAbelianVariety.poincare_coherent_transform`, with `sorry` as its
entire proof. It adds no definition or axiom. The node is unchanged except for `lean`.

The conclusion is the derived isomorphism in Mumford, Abelian Varieties, III §13,
pp.126–129, Corollary 1 p.129, rather than only a list of cohomology groups.
I read the primary scan named by the node at
https://djvu.online/file/2tC7xp3dbqGCh (printed pp.126–129, including the local
free complex, the reduced identity subscheme, and comparison with the Koszul
resolution). The theorem docstring carries all nine proof steps of the node,
including the dependencies and the dimension-zero argument.

Clause-by-clause correspondence:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
  There is no characteristic restriction, perfection hypothesis, or chosen algebraic closure.
- Abelian variety over k: `(A : Over (Spec (.of k))) [GrpObj A]
  [IsAbelianVariety A]`. The recorded upstream class supplies exactly properness,
  smoothness, and connectedness; `GrpObj` supplies the group scheme.
- Dimension g >= 0: the expression `IsAbelianVariety.dim A : ℕ` is the actual
  dimension, rather than an independently supplied bound. The upstream theorem
  `IsAbelianVariety.topologicalKrullDim_eq` identifies it with the recorded
  `topologicalKrullDim A.left`. Substituting this dimension for the node's g
  removes a redundant natural-number binder and equality hypothesis.
- Dual and universal normalized Poincare line: `(D : AbelianDualPoincareDatum A)`.
  This is the existing structure publicly imported by the recorded polarization
  calculus module. `D.dual` is an abelian variety; `D.poincare` is an invertible
  module on `(A ⊗ D.dual).left`. Its `universal` field is representability for
  rigidified fibrewise algebraically trivial families on all parameter schemes.
  `rigidification` and `otherAxis` supply the two identity-axis normalizations.
  Quantifying over this actual normalized datum does not choose a line module
  from a mere existence theorem or postulate a replacement canonical map.
- Product and second projection: `A ⊗ D.dual` and `(snd A D.dual).left`
  in the cartesian monoidal category of schemes over Spec k. These are the
  scheme fibre product and its second projection, not an abstract unrelated map.
- Identity e: `(η[D.dual]).left` is the group identity section. Its source is
  definitionally Spec k, the underlying scheme of the terminal object in `Over`.
- The reduced identity module with evaluation action: the exact object is
  `(RingedSpace.moduleDirectImage (η[D.dual]).left.toLRSHom.toShHom).obj
  (𝟙_ (Spec (.of k)).Modules)`. The tensor unit is the actual structure sheaf of
  Spec k. That scheme is a reduced one-point scheme; its pushforward has stalk k
  at the identity and zero away from it. `moduleDirectImage` acts on sections
  through the identity morphism's structure-sheaf map, so its scalar action is
  precisely evaluation at e, with no infinitesimal thickening and no arbitrary
  skyscraper action.
- Zariski module derived categories: the carriers throughout are the shared
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, definitionally the recorded
  `CategoryTheory.ringedSiteModules` specialization. They use Mathlib's existing
  category and abelian instances, not the separate category instance on
  `Scheme.Modules`. `D.poincare` and the structure-sheaf unit are supplied as
  objects of this common carrier.
- Derived direct image: `RingedSpace.derivedModuleDirectImage` of the underlying
  ringed-space second projection, exactly the recorded dependency. Its input is
  `(DerivedCategory.singleFunctor ... 0).obj D.poincare`, so the Poincare module
  starts in degree zero. It is the ordinary right derived pushforward on module
  sheaves, with K-injective resolutions, not a compact-support or etale functor.
- The right side first places the ordinary identity pushforward in degree zero
  with `DerivedCategory.singleFunctor ... 0`, then applies
  `⟦-(IsAbelianVariety.dim A : ℤ)⟧`. Mathlib's cochain shift convention is the
  node's `H^i(C[r]) = H^{i+r}(C)`, so it lies in degree g.
- Existence of an isomorphism in D(O_dual): `Nonempty ( ... ≅ ... )`.
  No canonical scalar normalization is asserted.
- The explicitly bound universes `u wP wB` and the two `HasDerivedCategory`
  instances specify the localization choices for the product and the dual.
  The independent morphism universes are retained. These are the choices needed
  to interpret the node's derived categories, not extra geometric hypotheses.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (the algebraic-closure dependency's
  `mathlib_match` explicitly records this algebraically-closed-field predicate).
- `AlgebraicGeometry.IsAbelianVariety`, `IsAbelianVariety.dim`, and
  `IsAbelianVariety.topologicalKrullDim_eq`,
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`.
- `topologicalKrullDim`, `Mathlib.Topology.KrullDimension`.
- `AlgebraicGeometry.IsAbelianVariety.exists_dual_polarization_calculus`,
  `Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`, and its public
  interface `AlgebraicGeometry.AbelianDualPoincareDatum` in
  `Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum`.
- `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.singleFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `CategoryTheory.ringedSiteModules`, `Sheaf.CategoryTheory.RingedSiteModules`,
  and its exact Mathlib carrier `SheafOfModules`.
- `AlgebraicGeometry.RingedSpace.derivedModuleDirectImage` and
  `AlgebraicGeometry.RingedSpace.moduleDirectImage`,
  `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage`.

The source signatures and docstrings were read, including the normalized datum's
universal property and both axes, the upstream dimension definition and its
Krull-dimension identification, and the K-injective derived-direct-image interface.
Statement dependencies are public imports; each already stated proof dependency
has a plain import. This includes Mathlib matches for Jacobson spaces,
single-degree concentration, projective-resolution homotopy equivalence, and
closed-point residue fields. The two proof dependencies still lacking a recorded
interface (`lem-sfb-regular-local-punctual-acyclicity` and
`lem-trf-proper-field-invertible-coherent`) are retained in the proof plan; neither
is needed to type the present statement.

Edge cases checked before writing:

- g = 0: the negative shift is zero and both the Poincare module and the identity
  module are degree-zero modules. There is no positive-dimension assumption.
- Positive characteristic, including characteristic two: no prime, integer
  invertibility, or characteristic-zero typeclass is present.
- Empty schemes: an abelian variety has a group identity section from nonempty
  Spec k, so the source assumptions themselves exclude emptiness; no new
  nonemptiness assumption has been added.
- The identity sheaf is supported on the reduced rational point; pushing forward
  O_(Spec k) cannot produce an unspecified finite-length thickening.
- Different valid normalized dual data are covered by the D binder. No selected
  polarization, ample line, basis, determinant trivialization, or isogeny is assumed.
- The source and target localization morphism universes remain independent.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder`: "The derived pushforward of the normalized Poincare
  bundle on an abelian variety times its dual is the skyscraper at the identity
  shifted by minus the dimension". Eight hits: the module-pullback unit and its
  adjunction formulas, `Scheme.Modules.pseudofunctor_map_r`, and additivity of
  module pullback/pushforward. None computes this transform.
- `msearch.py ... loogle`: `"poincare", "derivedModuleDirectImage"`.
  Zero hits.
- `msearch.py ... grep`: `Poincare|poincare|FourierMukai|Fourier.Mukai`, scope
  `Mathlib/AlgebraicGeometry`. Zero hits.
- `msearch.py ... leansearch`: "The Poincare line bundle has derived direct image
  the residue field at the identity shifted by the dimension". Eight hits about
  scheme/local-ring residue fields and their maps; none states the transform.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the same Poincare/Fourier
  patterns found etale Poincare duality and the existing abelian dual/Poincare
  datum, polarization calculus, biduality, and Picard-zero cohomology. None states
  the coherent derived transform. The exact item-id search in
  `lean/WeilConjectures` and `dag/lean_names_upstream.json` had no hits.

No new nodes, dependency repairs, statement corrections, or disputed statements
are needed. The only postponed theorem is the assigned node itself.

Validation: the prescribed `scompile.py NP lem-sfb-poincare-coherent-transform`
compiled the delivered module successfully in both sandbox and library module
modes (6.0 s and 4.1 s), with no errors or unexpected warnings. Every variable
and universe is explicit and auto-implicit elaboration is disabled. All lines
of the Lean file are at most 100 characters.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
