## Worker report

The module `Sheaf.AlgebraicGeometry.AdaptedSmoothAmbient` states
`AlgebraicGeometry.Scheme.Hom.exists_adapted_smooth_ambient` with one `sorry` and no
new definitions. The node is unchanged except for its `lean` record. There are no
new nodes, dependency repairs, statement corrections, or disputed clauses.

Source read: BLR, *Neron Models*, 3.3 Proposition 5, proof on printed pp. 68--69
(PDF pp. 74--75), in the primary-source scan linked in the node. Its first two
construction paragraphs choose free restricted differentials, form the polynomial
Jacobian smooth ambient scheme, lift the coordinate basis, and arrange the ideal
`J=(π,z₁,…,zₙ)`. The following density argument starts only at the claim `H ⊆ J²`;
that claim is outside this node. The construction does not need the generic
smoothness and density hypotheses used later in the proposition. The current
blueprint unit and chapter were read; this is a supporting lemma, not the unit's
own statement. The module docstring carries all ten accepted DAG proof steps and
their dependency ids.

Hypothesis correspondence:

- DVR: `R : CommRingCat.{u}`, `[IsDomain R]`, `[IsDiscreteValuationRing R]`.
  `π : R` and `hπ : Irreducible π` are precisely a uniformizer, by
  `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- Residue field: the actual canonical `IsLocalRing.ResidueField R`, with quotient
  map `IsLocalRing.residue R`. An arbitrary residue-field model is transported
  through its canonical isomorphism; no assumption on characteristic is imposed.
- The R-scheme X: `p : X ⟶ Spec R` and `[LocallyOfFiniteType p]`. The morphism
  is explicit because the differential declaration takes it and the special-fibre
  square compares several structure morphisms. X need not be quasi-compact.
- Closed `Y ↪ X_k`: `i : Y ⟶ X`, `[IsClosedImmersion i]`, its residue-field
  structure `q`, and `hq : i ≫ p = q ≫ Spec.map (CommRingCat.ofHom ...)`.
  This describes the composite closed immersion into X with its factorization
  through the special fibre, equivalently a closed subscheme of the fibre product.
  The map `Spec k → Spec R` is the canonical quotient closed immersion, so the
  induced immersion into `X_k` is closed, and conversely its composite is closed.
- Open smooth U: `U : Y.Opens` and `[Smooth (U.ι ≫ q)]`.
- Finite local freeness of the restricted relative differentials:
  `hfree : ((Scheme.Modules.tensorPullback (U.ι ≫ i)).obj
  p.relativeDifferentials).IsFiniteLocallyFree`. This is the recorded tensor
  pullback, with the existing varying-rank finite-locally-free predicate; neither
  Mathlib's other module pullback nor a constant global rank is substituted.
- Arbitrary point of U: `u₀ : U.toScheme`; its image in X is `i (U.ι u₀)`.
  The universe u is explicit and unrestricted, with all rings and schemes in the
  project's standard common universe. All variables are explicitly bound and
  `autoImplicit` and `relaxedAutoImplicit` are disabled.

Conclusion correspondence:

- The affine open neighbourhood is `V : X.Opens`, with `eD : V.toScheme ≅ Spec D`,
  and the first conjunct says `i (U.ι u₀) ∈ V`.
- W is the full scheme-theoretic inverse-image open `(i ⁻¹ᵁ V).toScheme`, not an
  arbitrary smaller open. The second conjunct is `i ⁻¹ᵁ V ≤ U`.
  `eE : (i ⁻¹ᵁ V).toScheme ≅ Spec E` identifies its coordinate ring E.
- Z is `Spec C`, with structure map `Spec.map a`. Smoothness, local finite type
  and quasi-compactness are all explicit, so Z is smooth affine finite type over R.
- The surjection `f : C ⟶ D` gives the closed immersion V → Z via `eD.hom` and
  `Spec.map f`. The equality `eD.hom ≫ Spec.map (a ≫ f) = V.ι ≫ p` makes it
  an R-immersion. `g : D ⟶ E` is surjective and its spectrum is exactly the
  inclusion of W in V, by the `eE.hom ≫ Spec.map g` equality. These specify
  actual coordinate-ring maps, rather than unrelated surjections.
- The two finite families of functions are `y : Fin r → C` and `z : Fin n → C`.
  `Fin.addCases y z` lists them in precisely that order.
- H and J are `RingHom.ker f.hom` and `RingHom.ker (f ≫ g).hom`.
  Their inclusion is explicit. The ideal equality is
  `RingHom.ker (f ≫ g).hom = Ideal.span ({a π} ∪ Set.range z)`.
  The isomorphism of Spec E with W and the two surjections identify E canonically
  with C/J, so this is the node's kernel into the global functions of W.
- The etale coordinate morphism is explicitly the spectrum of polynomial
  evaluation `MvPolynomial.eval₂Hom a.hom (Fin.addCases y z ...)`, followed by
  `AffineSpace.SpecIso ... R).inv`. The coordinate index `ULift.{u} (Fin (r+n))`
  uses the exact recorded affine-space construction, including r+n=0.
- `b : Module.Basis (Fin (r+n)) C (CommRingCat.KaehlerDifferential a)` proves
  freeness, and `∀ j, b j = ...d (Fin.addCases y z j)` fixes the basis vectors
  to the listed actual differentials. This bundled Kahler module is definitionally
  the recorded `KaehlerDifferential R C` for the algebra given by a.
- The isomorphism α has source E ⊗_C Ω(C/R) and target E ⊗_D Ω(D/R), the node's
  tensors with factors reversed. Its final formula for every c and e fixes
  `e ⊗ dc ↦ e ⊗ d(f c)`. These elements span the source, so the isomorphism
  is the canonical differential map, rather than an arbitrary isomorphism.
  ModuleCat.extendScalars supplies both actual tensor constructions and their
  E-linear structure without inventing independent algebra structures.
- `IsNoetherianRing C` is explicit. No generic smoothness, flatness of X, density,
  or group structure is assumed.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `irreducible_iff_uniformizer`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  the morphism restriction API is `Scheme.Hom.resLE` / `morphismRestrict`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, and the scheme pullback instance in
  `Mathlib.AlgebraicGeometry.Pullbacks`. The special-fibre and W squares are
  represented equivalently by the factorization and inverse-image restriction.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the public upstream
  `Scheme.Modules.tensorPullback`, built by the tensor formula, and its recorded
  `Scheme.Modules.tensorPullbackSectionAdjunction`. Only the functor is needed.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace`, `AffineSpace.SpecIso`.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `linearMapEquivDerivation`; the ring-map interface
  `Mathlib.Algebra.Category.ModuleCat.Differentials.Basic` supplies
  `CommRingCat.KaehlerDifferential` and its `d` with exactly these underlying data.
- The existing varying-rank predicate `SheafOfModules.IsFiniteLocallyFree` from
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, already
  publicly imported by the differential dependency, is the notion carried by
  `def-sc-finite-locally-free-sheaf`. No new definition is introduced.

All stated proof dependency modules are imported, using plain imports when only
needed by the proof. The two proof dependencies with no recorded declaration,
`lem-sfb-etale-localization-relative-differentials` and
`lem-sfb-smooth-morphism-cotangent-isomorphism-etale`, have no module to import;
they are not statement dependencies and no substitute theorem is invented here.

Edge cases checked before writing:

- Empty U or Y: the point binder has no inhabitants, so no neighbourhood is
  asserted for a nonexistent point. There is no added nonemptiness hypothesis.
- r=0 and n=0: `Fin.addCases`, the empty basis and the ideal span all remain
  defined. For X=Spec k, choose C=R, D=E=k and r=n=0; the differential map is
  0 → 0, and the ideal is (π).
- Smooth X with smooth special-fibre centre: ordinary etale coordinates give
  the expected example, with the differential map the identity after restriction.
- Nonflat X=Spec(R/(π²)), Y=Spec k: C=R and r=n=0 again work. Thus the interface
  does not silently require flatness. For X=Spec(R[t]/(t²)) with Y the origin,
  C=R[t], z=t, r=0,n=1 work, including residue characteristic 2. The differential
  of t remains the basis along the reduced centre.
- U may have components of different ranks or dimensions: hfree is varying
  rank, while the output r,n are chosen separately at the arbitrary point.
- No assumption that u₀ is a closed or rational point is present.

Searches actually run (all on 2026-10-24):

- msearch leanfinder: "A closed subscheme with locally free restricted
  differentials and smooth special fibre centre has local etale coordinates in a
  smooth ambient scheme". Eight hits: general standard-smooth charts and etale
  polynomial coordinates, not this ambient embedding and restricted isomorphism.
- msearch loogle: `KaehlerDifferential, Algebra.Smooth`. Zero hits.
- msearch grep: `adapted.*smooth|smooth.*ambient|cotangent.*embedding`.
  One Mathlib hit, the general cotangent-complex comment in
  `Mathlib/RingTheory/Extension/Cotangent/Basic.lean`, not this statement.
- msearch leansearch: "Smooth ambient scheme with etale coordinates adapted to a
  smooth closed subscheme and isomorphism on restricted Kahler differentials".
  Eight hits: general smoothness/etale predicates and their constructors, not an
  exact match or one-line specialization of this statement.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `adapted.*smooth|smooth.*ambient|lem-sfb-adapted-smooth-ambient`, and a search for
  the chosen declaration name also in `dag/lean_names_upstream.json`.
  The broader hits include `RingTheory/Etale/Coordinates.lean`,
  `SmoothPairLocalCoordinates.lean` and `CotangentIsomorphismCoordinateLift.lean`.
  These concern already smooth ambient schemes or compatibility between two
  embeddings, not existence of this smooth ambient with the restricted
  differential isomorphism. No node-id or declaration-name match exists.
- Read the existing finite-locally-free-sheaf node and its recorded declaration;
  it already supplies the variable-rank notion used by hfree.

Validation: scompile.py compiled the sandbox module and the actual library-path
module cleanly in module mode (2.2 s and 2.7 s respectively), within the fixed
60-second per-file limit. An initial elaboration error on shorthand `.ofHom` was
repaired by spelling `CommRingCat.ofHom` explicitly. No #check probes remain.

## Second reading by O3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
