## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothFixedResidueArtinianTest` states
`AlgebraicGeometry.smooth_near_of_fixed_residue_artinian_lifting`, with `sorry` as
its only proof. It states precisely Stacks 02HX (4) implies (1) in the node's
marked-residue-field formulation. There are no new definitions, dependency
repairs, or statement corrections. The accepted stage-1 split is unchanged.

The inherited ending reported a stage-1 unchanged-item refusal. The current
assignment is stage 2: the current node is split and reviewed, has no Lean record,
and is a stage-2 entry in `coord/queue.tsv`. No released repair note exists for
this id. The preserved sandbox contained only dispatcher brief markers. This
packet adds the missing Lean attachment and theorem rather than changing the
accepted split. The old stage-1 refusal does not apply to this packet.

Clause-by-clause correspondence:

- Schemes and morphism `f : X → Y`: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
- Locally of finite type: `[LocallyOfFiniteType f]`. No quasi-compactness or
  global finite-type hypothesis is added.
- Locally Noetherian target: `[IsLocallyNoetherian Y]`.
- Point `x` and its actual residue field: `(x : X)` and `X.residueField x`.
  No arbitrary field or coefficient-field embedding replaces this field.
- Every pair of commutative test rings: `∀ (B' B : CommRingCat.{u})`.
  The bundled rings supply their commutative ring structures. Test spectra and
  `X`, `Y` inhabit the same scheme category. The common universe `u` contains
  the actual residue field and every finite quotient/localization test used
  by the proof; there is no independent, potentially smaller test universe.
- Artinian and local on both rings: `[IsArtinianRing B'] [IsArtinianRing B]
  [IsLocalRing B'] [IsLocalRing B]`. The Artinian predicate is DCC for the
  lattice of ideals (the ring as its own module), and locality is Mathlib's
  equivalent nontrivial local-ring predicate, hence unique maximal ideal.
- A small extension: `(q : B' ⟶ B)`, `Function.Surjective q.hom`, and
  `Module.length B' (RingHom.ker q.hom) = 1`. This is literally the definition
  in Algebra Tag 02HS. The equivalent description as a one-dimensional
  residue-field module annihilated by the maximal ideal is a consequence,
  not an added hypothesis or a weaker square-zero-only test.
- Specified compatible residue-field identifications: universally quantify
  `(r : B ⟶ X.residueField x)` with `Function.Surjective r.hom`. A surjective
  map from a local ring to a field has its unique maximal ideal as kernel,
  and induces exactly an isomorphism `B/m_B ≅ κ(x)`. The composite `q ≫ r`
  is surjective and likewise identifies the residue field of `B'` with
  `κ(x)`. Under these identifications `q` induces the identity. Conversely,
  every pair of residue identifications respected by `q` is recovered this
  way: the one for `B'` is forced by that for `B`. Thus no independent
  marking has been dropped and no special algebra structure is required.
- Every map `a : Spec B → X` with the required restriction: quantify
  `(a : Spec B ⟶ X)` and require
  `Spec.map r ≫ a = X.fromSpecResidueField x`. This equality is of scheme
  morphisms, not merely an equality of images of closed points. It expresses
  exactly the canonical marked point in the node and the isomorphism on
  residue fields of Stacks 02HX (4).
- Every compatible map `b : Spec B' → Y`: quantify `(b : Spec B' ⟶ Y)`
  and require `a ≫ f = Spec.map q ≫ b`. This is the stated commutative square.
- Existence of the prescribed lift with both equalities:
  `∃ a' : Spec B' ⟶ X, Spec.map q ≫ a' = a ∧ a' ≫ f = b`.
  The residue restriction for `a'` follows from the first equality and the
  marking for `a`, since the marking on `B'` is `q ≫ r`.
- Open neighbourhood and smooth restriction:
  `∃ N : X.Opens, x ∈ N ∧ Smooth (N.ι ≫ f)`. An element of `X.Opens` has
  its canonical open subscheme and inclusion `N.ι`; their composite with
  `f` is precisely the requested restriction. No affineness condition on
  `N` or smoothness away from `N` is asserted.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `AlgebraicGeometry.Scheme.residueField`; the canonical point is the same
  module's `Scheme.fromSpecResidueField`, defined using the residue map of
  the stalk and `Scheme.fromSpecStalk`.
- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `Spec.map`.
- `def-sbc-smooth-morphisms`:
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, the already recorded affine-local notion
  identified with formally smooth and locally finitely presented by 02H6.
- `Mathlib.RingTheory.Length`, `Module.length`, gives the exact length-one
  condition without a duplicate definition of small extension.

Statement dependencies are public imports. Plain proof imports provide the
recorded polynomial-ring, localization, Noetherianity, open-factorization and
unique-prime Mathlib matches: `MvPolynomial`, `Localization.AtPrime`,
`Algebra.FiniteType.isNoetherianRing`, `IsLocalization.isNoetherianRing`,
`AlgebraicGeometry.IsOpenImmersion.lift`,
`IsArtinianRing.isMaximal_of_isPrime` and `IsLocalRing.eq_maximalIdeal`.
The smooth-affine comparison and smooth-open restriction proof matches are
already in the public smooth module. The two proof-only nodes
`lem-sfb-fixed-residue-lifts-truncated-section` and
`lem-sfb-truncated-polynomial-sections-smooth` currently have neither Lean
records nor Mathlib matches, so their future modules cannot yet be imported;
the full six-step plan and their ids are in the theorem docstring. They are
not notions needed to type this statement. No existing dependency interface
is copied or replaced.

Edge cases checked before writing:

- Empty `X` has no point `x`; the point binder makes the assertion correctly
  vacuous. A morphism with a supplied point cannot have empty target.
- The zero ring is excluded by locality, as in the source's unique-maximal-
  ideal convention; no artificial empty-spectrum small extension appears.
- A field is allowed for `B`, with `B'` for example dual numbers. Identity
  maps, having zero kernel length, are correctly not small extensions.
- Mixed-characteristic small extensions are included, for example
  `Z/p² → F_p`. A section `κ(x) → B'` is nowhere assumed.
- All residue-field automorphisms are allowed through the quantifier over
  `r`, but only `a` with the exact canonical marked restriction is tested.
  Replacing this by a closed-point equality would give the wrong criterion.
- Purely inseparable field extensions are not incorrectly declared smooth.
  In characteristic `p`, for `K = F_p(s)` and `L = K[t]/(t^p-s)`, the test
  `B' = K[t]/((t^p-s)^2) → B = L` has residue field `L` and length-one kernel.
  A `K`-algebra lift of `L` would lift `t` to an element whose `p`th power
  is `s`; adding a multiple of the square-zero kernel cannot remove the
  nonzero error `t^p-s`, so this required test fails.

Searches for an existing statement:

1. `msearch.py ... leanfinder` query
   `Smoothness at a point from lifting small extensions of Artinian local rings with fixed residue field`:
   eight hits, including `Algebra.IsSmoothAt`, `Algebra.Smooth`,
   `Algebra.Smooth.formallySmooth`, `RingHom.IsStandardSmooth.smooth`,
   `RingHom.Smooth.propertyIsLocal`,
   `AlgebraicGeometry.instHasRingHomPropertyIsSmoothLocallyIsStandardSmooth`,
   `Algebra.instSmoothOfIsStandardSmooth`, and
   `RingHom.Smooth.locally_isStandardSmooth`. None states the fixed-residue
   small-extension implication at a scheme point.
2. `msearch.py ... loogle` query
   `AlgebraicGeometry.Smooth, IsArtinianRing`: zero hits.
3. `msearch.py ... grep` query
   `Artinian.*[Ll]ift|[Ll]ift.*Artinian|residue.*[Ss]mooth|[Ss]mooth.*residue`
   in `AlgebraicGeometry`: five lines, all from Mathlib's `SmoothFiber.lean`;
   its fibre criterion assumes flatness and is a different statement.
4. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for Artinian lifting,
   fixed-residue spellings, and small-extension names located the upstream
   `WeilConjectures.AlgebraicGeometry.SmoothArtinianLiftingAtPoint` and its
   ring version `SmoothAtPrimeArtinianLifting`. I read their full statements
   and docstrings. `smooth_near_iff_artinian_lifting_at_point` treats 02HX
   (1) iff (3), testing all residue extensions and requiring just that the
   closed point maps to `x`. It does not state 02HX (4) implies (1); using its
   reverse implication here would require the stronger lifting hypothesis.
   The ring theorem likewise tests arbitrary residue-field extensions.
   `ProperCurveVersality` uses the same surjective-residue-map encoding for
   a different notion, not a duplicate of this criterion.
5. `rg` for the exact item id and proposed declaration name in the upstream
   library, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no matches.

Source verification: read the full statement and affine-reduction proof of
`more-morphisms.tex`, `lemma-lifting-along-artinian-at-point` (Tag 02HX),
and the small-extension definition and reverse smoothness proof in
`algebra.tex`, `definition-small-extension` / `lemma-smooth-test-artinian`
(Tags 02HS / 02HT). No statement fault or dispute was found.

Validation: `scompile.py Q38 lem-sfb-smooth-fixed-residue-artinian-test` compiled
this module in both sandbox and library modes, cleanly within the 60-second
limit (3.6 s and 5.6 s respectively). `autoImplicit` is disabled and the sole
universe and every variable are explicitly bound. Only the `lean` field in
the copied node was changed. Delivery preflight is run through `deliver2.py`.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
