## Worker report

The delivery states `AlgebraicGeometry.multiplicativeIsogeny_borel_comparison` in
`Sheaf.AlgebraicGeometry.GroupScheme.MultiplicativeIsogenyBorelComparison`.
Its only theorem proof is `sorry`; there are no new definitions or axioms.
I read the node, all eight original statement dependencies and their recorded
declarations, and Milne, Algebraic Groups (2017), printed pp.390–392
(PDF pages 402–404), especially Proposition 18.18 and its displayed middle row.
The source assumes split groups here; over the node's algebraically closed field
this is automatic, as Milne explicitly says on p.390. No source correction is needed.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  Arbitrary `u` retains every field size covered by the existing scheme library.
- The affine finite-type F-group schemes are `G₁ G₀ : Grp (Over (Spec (.of F)))`,
  `[IsAffine Gᵢ.X.left]`, `[LocallyOfFiniteType Gᵢ.X.hom]` and
  `[QuasiCompact Gᵢ.X.hom]`. These are the precise dependency conventions.
- Smoothness and connectedness are `[Smooth Gᵢ.X.hom]` and
  `[ConnectedSpace Gᵢ.X.left]` for both groups. ConnectedSpace includes nonemptiness.
- The homomorphism is `f : G₁ ⟶ G₀`. Bundled group morphisms supply IsMonHom.
  Its coordinate ring map is `f.hom.hom.left.appTop.hom`; `hf` requires its
  FaithfullyFlat predicate, namely exact scalar extension detecting zero modules.
- The scheme-theoretic kernel N is `GrpObj.ker f.hom.hom`, not a reduced kernel
  or an abstract group of geometric points. Its finiteness is
  `[IsFinite (GrpObj.ker f.hom.hom).hom]`, equivalent over a field to a
  finite-dimensional coordinate algebra. `hN` uses
  `IsFiniteDiagonalizableGroupScheme` on that exact kernel. The recorded
  definition is natural identification of all scheme-valued points with
  Hom(M, global units) for a finite abelian M, equivalent to Spec F[M] with the
  indicated Hopf operations. It preserves nonreduced groups such as μ_p.
- An arbitrary Borel is `B₀` with `i₀ : B₀ ⟶ G₀` and `hB₀`.
  `IsBorelGroupScheme` means maximal smooth connected solvable closed subgroup;
  its solvability uses the smallest-closed-subgroup derived series, as in the node.
  Borel affineness and finite type follow from its closed embedding into G₀,
  so no extra assumptions on B₀ are imposed.
- The existential `B₁, i₁, fB` has
  `IsPullback i₁.hom.hom fB.hom.hom f.hom.hom i₀.hom.hom`.
  This identifies B₁ with the scheme-theoretic inverse image, including its
  group structure and the actual restriction of f, independent of a chosen
  fibre-product representative. `IsBorelGroupScheme i₁.hom.hom` is the first claim.
- `fB.hom.hom.left.appTop.hom.FaithfullyFlat` is the asserted faithful flatness.
  The bundled `n : Grp.mk N ⟶ B₁` satisfies
  `n.hom.hom ≫ i₁.hom.hom = GrpObj.kerι f.hom.hom`.
  The following IsPullback square over `η[B₀.X]` says that this same N, with its
  original embedding in G₁, is the full kernel of fB. It is not an arbitrary
  isomorphic kernel with an unspecified restriction map.
- Characters of B₀, B₁ and N are the respective bundled group-scheme Hom types
  into `Grp.mk (StandardGroupSchemes.multiplicative F)`. This is exactly X*, with
  abelian operation pointwise multiplication of values; no character lattice
  is replaced by an abstract group or a group of F-points. Injectivity is
  `Function.Injective (fun χ ↦ fB ≫ χ)`. Middle exactness is the equivalence
  between the actual restriction to N being the unit-valued morphism and
  existence of ψ with `fB ≫ ψ = χ`. This includes both image-in-kernel and
  kernel-in-image. Surjectivity is `Function.Surjective (fun χ ↦ n ≫ χ)`.
  These are precisely short exactness of the stated abelian character groups;
  no arbitrary maps or additional chosen group laws are introduced.
- `Q₁ Q₀` are F-schemes with quotient arrows `q₁ q₀`.
  The presheaf coequalizers of projection and `(g,b) ↦ g i(b)` are the right-coset
  presheaves. Each η has `coequalizer.π _ _ ≫ η = yoneda.map q`.
  Representability is by the displayed Q, IsSheaf requires the represented
  presheaf to be an fppf sheaf, and bijectivity of precomposition with η into
  every fppf sheaf is exactly the sheafification universal property.
  Thus these are the quotients specified in the node, not arbitrary schemes.
  The existing `Scheme.fppfTopology.over (Spec (.of F))` is used. Mathlib uses
  jointly surjective flat locally finitely presented coverings; refining their
  sources by affine opens gives the same topology as finitely presented covers
  in the node. No change of quotient convention results.
- `∃ e : Q₁ ≅ Q₀, q₁ ≫ e.hom = f.hom.hom ≫ q₀` gives the isomorphism with
  precisely the formula `gB₁ ↦ f(g)B₀`, on all test schemes.
- The preliminary Pic(G) sentence introduces notation unused in this node's
  conclusions, as also noted in its stage-1 review. No Picard-group assertion is
  made or omitted by this theorem.

Dependency declarations read and reused:

- `Field`, Mathlib.Algebra.Field.Defs, and `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic. The latter is explicitly named in the
  algebraic-closure dependency's mathlib_match alongside AlgebraicClosure.
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Grp; `GrpObj.ker`, `GrpObj.kerι`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp; and
  AlgebraicGeometry.IsFinite, Mathlib.AlgebraicGeometry.Morphisms.Finite,
  all exposed by WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `AlgebraicGeometry.LocallyOfFiniteType` and `QuasiCompact`, in the Mathlib
  Morphisms.FiniteType and Morphisms.QuasiCompact modules respectively.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and
  `multiplicativeGroup`, Sheaf.AlgebraicGeometry.StandardGroupSchemes:
  the actual Laurent-polynomial Hopf group scheme of def-sc-gm-ga.
- `AlgebraicGeometry.Scheme`, Mathlib.AlgebraicGeometry.Scheme, and
  `IsAffine`, Mathlib.AlgebraicGeometry.AffineScheme, for def-pc-scheme.
- `IsBorelGroupScheme`, Sheaf.AlgebraicGeometry.GroupScheme.Borel, and
  `IsFiniteDiagonalizableGroupScheme`,
  Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme, are existing landed
  definitions. Their definition-node ids are added to stmt_deps, as permitted
  for already landed notions. Their node files are unchanged.

All six proof steps are recorded in the theorem docstring. The six proof
dependencies with Lean modules are imported privately: BorelQuotientLifting,
BorelSchemeNormalizer, HomogeneousOrbitQuotientGeometry, HomomorphismFactorization,
MonomorphismClosedImmersion, MultiplicativeCharacterAntiduality. The three generic
Mathlib leaves (covering base change, representable descent, Yoneda) are available
through the site/Yoneda imports. The remaining five proof nodes have no recorded
module and are not needed for elaborating the statement. No proof of the item
is attempted here. The downstream CharacterPicardIsogenySequence module already
defines a precomposition homomorphism, but importing that consumer would create
a dependency cycle; this theorem instead writes the same composition functions
directly, without duplicating that definition.

Edge cases checked against the statement before writing: the identity isogeny
(trivial kernel, quotient comparison identity); solvable groups (Bᵢ = Gᵢ and
point quotients); SL₂ → PGL₂ (kernel μ₂); and t ↦ t^p on G_m in characteristic
p (nonreduced μ_p kernel and the character map ℤ → ℤ/p). No assumption on
characteristic, reductivity, semisimplicity, nontrivial kernel or positive
dimension occurs. Empty groups are correctly excluded by connectedness and the
identity section, rather than by an unrelated hypothesis. Tests use all
scheme-valued points, so an infinitesimal kernel is not lost.

Searches actually run through the prescribed msearch.py wrapper:

- leanfinder: "Multiplicative isogeny inverse image Borel subgroup flag quotient
  isomorphism short exact character sequence". Eight hits about abstract group
  quotients/Galois categories; none states this algebraic-group assertion.
- loogle: "CategoryTheory.GrpObj, CategoryTheory.IsMonHom". Twelve hits including
  Grp.ofHom and Grp.mkIso'; these confirm the existing group-object API, but
  give no Borel or character comparison theorem.
- grep: "IsBorel|multiplicativeIsogeny|borel.*isogeny|isogeny.*borel".
  Zero Mathlib hits.
- leansearch: "A multiplicative isogeny induces an isomorphism of Borel quotients
  and an exact sequence of Borel character groups". Eight abstract quotient,
  character-module and measurable-Borel hits; no matching statement.
- Direct rg over the project's Sheaf and WeilConjectures trees for Borel,
  diagonalizable, character, and multiplicative-isogeny names found the reusable
  definitions and distinct theorems listed above. A search by the item id in
  WeilConjectures found no declaration. The proposed theorem name was also
  searched in Mathlib, both project roots and dag/lean_names_upstream.json;
  it was unused. No exact existing theorem was found.

Validation: scompile.py compiled the sandbox and final module independently
against the server's published library, in 2.7 s and 2.1 s, with no errors or
unexpected warnings. Every variable and universe is explicit; autoImplicit is
false. No statement correction, new node, or dependency-module repair is needed.

## Second reading by Q120

This is a separate self-check pass by the dispatched worker; the dispatch brief
forbids starting other agents, and the maintainer supplies the independent review.
I reopened the source node and the complete resulting signature. Both groups
have exactly affine/finite-type/smooth/connected assumptions, f is the specified
faithfully flat homomorphism, and N is the finite diagonalizable scheme kernel.
The Borel predicate's maximality and derived-series convention agree word for
word with the informal notion. The inverse-image square has the right legs:
i₁ followed by f equals fB followed by i₀. The kernel square has top leg n,
bottom leg the unit section of B₀, and its embedding agrees with kerι f.
The two character maps are precomposition by these exact arrows. Triviality is
equality to the constant identity morphism on N, not equality on rational points.
Both coset coequalizers use right multiplication, and the η generator equations
tie them to q₁ and q₀. The final equation has source G₁ and target Q₀ and fixes
the required coset formula. No mismatch was found; no mathematical statement
was changed. The only node changes are lean and the two landed definition ids
added to stmt_deps. No local notation, local instance or hidden choice occurs.
