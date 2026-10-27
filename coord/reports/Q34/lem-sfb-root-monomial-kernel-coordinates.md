## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RootMonomialKernelCoordinates`
states `AlgebraicGeometry.RootMonomial.root_monomial_kernel_coordinates` with
one `sorry`, and defines three coordinate helpers with complete data:
`factor F q` is exactly Spec F[z]/(z^q), `factorι` is induced by the quotient
algebra homomorphism, and `orderedMap` multiplies the ordered negative factors,
then the middle factor, then the ordered positive factors. These are the
coordinate objects and maps introduced in this node, rather than independent
replacement definitions of group schemes, root groups, or root data.

Hypothesis correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`;
  `(p : ℕ) [ExpChar F p]` is the characteristic exponent, including p=1 in
  characteristic zero. All universes are declared and autoImplicit is false.
- `G,T : Fin 2 → Grp (Over (Spec (.of F)))` and `iT` give both pairs. `hG`,
  `hT`, `hsplit` say reductive, maximal torus, and split. The two commutativity
  instances expose the actual additive character/cocharacter Hom groups.
- `aG,hconj` identify the action with conjugation. `Φ,D,hred,hroot,hpair,hweights`
  give the reduced root data of the recorded Borel-pair theorem: roots are the
  actual nonzero torus character weights and the pairing is composition with
  integer power maps on G_m. No arbitrary abstract replacement lattice is used.
- `U,iU,hU` give the smooth connected closed normalized root subgroups with
  their prescribed tangent weight spaces, exactly the interface of the recorded
  root-subgroup theorem. `x` is an arbitrary family of group-scheme isomorphisms
  from G_a. No choice of scale or pinning is imposed.
- `f` is the already given group-scheme homomorphism. `h,hfT` specify its torus
  restriction; `u,hu` specify pullback on actual characters. `hinj,hfinite` are
  injectivity and finite cokernel. `b` is the root bijection, `q,hq` are the
  characteristic-exponent powers. `hrootmap,hcorootmap` are exactly the two
  displayed root and coroot equalities; cocharacter pushforward is composition
  with the specified h, so no unrelated dual map is assumed.

Conclusion correspondence:

- `Surjective f.hom.hom.left` is surjectivity of the scheme morphism.
- `f.hom.hom.left.appTop.hom.FaithfullyFlat` is faithful flatness of the actual
  coordinate ring map. Mathlib defines this by `Module.FaithfullyFlat` for the
  induced algebra structure, hence extension of scalars is exact and detects zero.
- `IsFinite (GrpObj.ker f.hom.hom).hom` states finiteness of the actual
  scheme-theoretic kernel. Over the field, this is equivalently finite-dimensional
  global coordinate algebra, as the recorded group-scheme convention specifies.
- `∃ c : Φ 1 → Fˣ, ∀ α A ... a, ...` is precisely the unit coefficient monomial
  formula. It uses the recorded `additiveParameterPoint` and the algebra map F→A,
  for every commutative F-algebra in the base universe, including nonreduced A.
  This is the usual functor-of-points test for these F-schemes; their universal
  coordinate algebras also live in this universe.
- For every root-datum `base` and every pair of enumeration equivalences `neg,pos`,
  `IsOpenImmersion` and `DenseRange` of the explicit ordered multiplication give
  its isomorphism onto the dense open big cell. On a root-datum Base every root
  has nonzero height, so `¬ base.IsPos` is exactly the negative system. Both
  orders are arbitrary and independent, not tied by negation.
- The inclusion of the range of `kerι` in that multiplication map's range is the
  assertion that the cell contains the whole kernel, including its nonclosed points.
- The existential `e` is an isomorphism **in Over (Spec F)** from the displayed
  product of the quotient spectra and `GrpObj.ker h.hom.hom` to the kernel of f.
  Its equality `e.hom ≫ kerι = orderedMap ...` pins it to the exact multiplication
  coordinates and the specified embeddings through `factorι`, `x`, and `iU`.
  It does not equip the factors with a product group law or assert a group isomorphism.
- The pullback square `IsPullback η[T₁] η[U₁α] iT₁ iU₁α` expresses that their
  scheme-theoretic intersection is the terminal F-scheme with its identity maps.
- `IsIso (toUnit (factor F 1))` states explicitly the q=1 trivial-scheme convention.
  No assumption of reducedness, smoothness, or etaleness of the kernel is present.

Dependency declarations read and used:

- `Field` in Mathlib.Algebra.Field.Defs; `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic; `ExpChar` in Mathlib.Algebra.CharP.Defs.
- `CategoryTheory.GrpObj`/`Grp` in Mathlib.CategoryTheory.Monoidal.Grp and
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The latter documents
  group schemes, `IsFinite`, and the scheme-theoretic `GrpObj.ker`, `kerι`;
  their actual construction is the identity pullback in
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp.
- `AlgebraicGeometry.reductive_borel_pair_structure` in
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure. Its signature
  supplies exactly the action, character/coroot, reduced RootDatum and Base interface.
  Its shared `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus` terminology
  is used directly, as are Mathlib `RootDatum` and `RootPairing.Base`.
- `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`,
  `additiveParameterPoint`, `weightSpace`, and `IsStable`, through
  Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations and
  its public imports. Its full root-subgroup signature and proof docstring were read.
- `StandardGroupSchemes.affine`, `map`, `additive`, `multiplicative` from the
  shared standard-group module supply the actual parameter lines and quotient spectra.
- Recorded proof modules are imported privately: MultiplicativeCharacterAntiduality,
  BruhatLongestCellCharts, BorelRootProductCoordinates, ReductiveRankOneReflections,
  AffineHomomorphismFlatImage, HomomorphismFactorization, SmoothGroupOrbitGeometry,
  and ReductiveTorusSelfCentralizer. Mathlib's finite-type/Jacobson and
  algebraically-closed residue-field modules are also imported privately. The
  regular-cocharacter proof node has no Lean record, so no invented import is used.

Sources were read from the supplied Milne PDF using pdftotext: Lemma 23.10,
printed p.487; Proposition 23.5, pp.485–486, especially (144)–(148); Theorem
21.84 and Summary 21.86, p.451. They agree with the node. The theorem docstring
retains all eleven proof steps, including rank-one nonvanishing, the finite open
kernel argument, and the final scheme-theoretic containment argument.

Edge cases checked before and after writing: root-free tori (empty products are
terminal objects, so the source of the kernel isomorphism is the torus kernel);
q=1 (the actual quotient F[z]/(z), and the explicit terminal-map isomorphism);
positive characteristic with q>1 (the quotient retains its nilpotents);
characteristic zero via ExpChar F 1; arbitrary rescaling of both root parameters;
nonreduced test algebras and kernels; and characteristic two in the source proof.
No statement correction or dispute was needed.

Searches for existing statements:

- msearch.py leanfinder: “A reductive group scheme homomorphism with a finite
  index torus lattice map has monomial root maps and a kernel product of
  infinitesimal root kernels”: 8 hits, chiefly RootPairing.Hom.root_weightMap,
  RootDatum, and abstract root-pairing lemmas; no group-scheme kernel result.
- msearch.py loogle: `RootPairing.Hom, AlgebraicGeometry.Scheme.Hom`: 0 hits.
- msearch.py leansearch: “A reductive algebraic group homomorphism with injective
  finite cokernel character lattice and compatible root powers has finite scheme
  kernel”: 8 hits, ring finiteness, abstract finite groups, IsFinite, and ideal-sheaf
  Scheme.Hom.ker; none is the required theorem. RootSystem/Hom.lean was read:
  its Hom preserves roots without p-powers, and isogenies are explicitly TODO.
- msearch.py grep: `rootSubgroup|rootGroup|bigCell|root_monomial`: 0 Mathlib hits.
- rg over lean/WeilConjectures and lean/Sheaf for
  `root.monomial|root_monomial|kernel.coordinates`: only unrelated polynomial,
  Galois-unit, conormal, and sheaf-section statements. A separate grep for this
  node id under lean/WeilConjectures had no hit. The upstream-name index had no
  matching declaration. The existing BorelRootProductCoordinates statement was
  read; it concerns the positive radical and supplies neither the recognition
  criterion nor the full kernel coordinates. Thus no exact existing match exists.

The final module compiles via the prescribed scompile.py; no local Lean build or
live-file mutation was performed. Only the node's lean field is changed.

## Second reading by Q34

A separate in-session rereading compared the completed node and module after the
first successful server compile. This is a self-check; the dispatcher prohibits
starting other agents, and the maintainer supplies the independent review.

The check followed the actual two displayed formulas and every conclusion:
`hu` fixes the lattice map to h, `hcorootmap` uses the genuine cocharacters,
`c : Φ 1 → Fˣ` excludes zero, and A is not restricted to fields. The negative
and positive products have arbitrary orders. The final e is an Over-category
isomorphism with its composition over G₁ specified, not a bare abstract isomorphism.
The cell's kernel containment is stated separately, and the intersection is a
pullback of schemes rather than equality only on rational points. Empty products
and the full nilpotent quotient spectra are retained. This reading added the
explicit `IsIso (toUnit (factor F 1))` conclusion to render the q=1 convention
literally. An import-visibility issue with the character abbreviations was repaired
by writing the exact Hom types already used in the dependency's signature. All
helper definitions have actual data; the theorem's whole proof is `sorry`.
