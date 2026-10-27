## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.GroupScheme.BruhatLongestCellCharts`.
Declaration: `AlgebraicGeometry.bruhat_longest_cell_charts`.
This is a theorem statement with one `sorry`; there are no definitions or proofs.
The source is Milne, Algebraic Groups (2017), 21.70--21.80 and 21.84--21.86,
printed pp.446--452, read from the local PDF using pdftotext. In particular 21.72
specifies the root-reversing involution, 21.79 specifies the orbit isomorphism,
21.80(b) specifies multiplication, and 21.84 specifies the scheme intersection.
The eight proof steps of the accepted DAG split are reproduced in the docstring,
including its repair of the gap in the printed proof of 21.71.

Hypotheses, one by one:

- F algebraically closed: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Reductive F-group scheme: `G : Grp (Over (Spec (.of F)))` and
  `hG : ReductiveTorusCentralizer.IsReductive G`. This is exactly the predicate
  used by the Borel-pair dependency: affine finite type, smooth, connected, with
  trivial smooth connected normal unipotent radical. Over algebraically closed F,
  its algebraic-closure formulation is equivalent to the node's formulation.
- Split maximal torus: `T`, `iT`, `hT : IsMaximalTorus iT`, and `hsplit` giving
  an isomorphism to the actual split torus of some rank, including rank zero.
- Borel containing T: `B`, `iB`, `hB : IsBorelGroupScheme iB.hom.hom`, and
  `j : T ⟶ B` with `hj : j ≫ iB = iT`.
- Its unipotent radical: `V`, `iV`, and `hV` exactly reproduce the closed,
  normal, smooth, connected, unipotent and largest-subgroup clauses of the
  radical supplied by `reductive_borel_pair_structure`. There is no arbitrary
  subgroup choice or additional complement hypothesis.
- Right B-torsor π: `Q`, `π`, `hπflat`, `hπsurj`, `hπinv`, `hπtorsor` reproduce
  the dependency's quotient invariance and torsor kernel-pair formula. Properness
  and finite type of Q are consequences of that quotient description, and need
  not be extra assumptions. An arbitrary presentation of the same quotient is
  allowed, so no chosen Q or section is assumed.
- Positive roots Φ⁺ and their number N: `aB` with `haB` pins the actual
  conjugation action, exactly as in the dependency. `hΦplus` identifies `Φplus`
  with precisely the nontrivial character weights on Lie(B), the positive roots
  in that dependency. No abstract unrelated root system or differential weights
  are substituted. `Φplus.card` is N. A full root datum and its base are not
  needed as extra inputs because their positive roots have this characterization.
- W and its action: the actual `RankOneRoots.Weyl iT` is the rational normalizer
  quotient, not the abstract root-datum Weyl group. Its action `act` is obtained
  existentially and pinned to conjugation by every representative on every test
  scheme. Precomposition with `(act w).inv` gives exactly χ(n_w⁻¹ t n_w).

Conclusions, clause by clause:

- W is finite: `Finite (RankOneRoots.Weyl iT)`.
- Unique longest element and involution: the first `Set.image` equality says
  w₀Φ⁺ = -Φ⁺. Inverses of the underlying character morphisms are the negative
  characters. The following universal implication gives uniqueness and
  `w₀ * w₀ = 1` gives involutivity.
- Representatives for every w: `n : Weyl iT → normalizer iT` with
  `∀ w, QuotientGroup.mk (n w) = w`.
- Locally closed smooth strata: `C`, `c`, `IsImmersion (c w).left` and
  `Smooth (C w).hom`. `∀ x, ∃! w, x ∈ Set.range (c w).left` gives the
  disjoint exhaustive partition on underlying points. The next clause gives
  the same unique stratum factorization for points over every algebraically
  closed extension K/F. These are the base changes of the same immersed schemes;
  base change of their isomorphisms and immersions is automatic. Algebraically
  closed residue fields detect every point of each scalar-extended scheme.
- Subschemes V^w of V: `Vw`, `v`, `IsImmersion (v w).left`.
- Multiplication V^w × B ≅ C_w: `e w` is an isomorphism in `Over (Spec F)`.
  Its composite with `c w` is explicitly `(u,b) ↦ u n_w b`, using the
  radical inclusion followed by iB and the constant representative.
- Longest stratum open dense: `IsOpenImmersion (c w₀).left` and
  `DenseRange (c w₀).left`.
- V^w₀=V as subschemes: `IsIso (v w₀)` says exactly that the inclusion
  represents the whole subscheme. Literal equality of arbitrarily presented
  scheme objects is neither necessary nor an invariant meaning of this clause.
- V is affine N-space: `Nonempty (V.X ≅ StandardGroupSchemes.affine F
  (MvPolynomial (Fin Φplus.card) F))`. This is Spec F[x₁,...,x_N] over F,
  including zero variables, not an abstract scheme isomorphism forgetting F.
- Both G and Q geometrically integral: `GeometricallyIntegral G.X.hom` and
  `GeometricallyIntegral Q.hom`; the Mathlib definition quantifies over all
  field extensions and includes nonemptiness, irreducibility and reducedness.
- Every representative n₀ of w₀: the remaining clauses are under `∀ n₀` and
  `QuotientGroup.mk n₀ = w₀`, independently of the selected representatives n.
- B∩n₀Bn₀⁻¹=T: equality of the two subsets of `A ⟶ G.X` for every
  `A : Over (Spec F)`. The left subset spells out membership in B and its
  conjugate; the right is the image of T. Testing every scheme, including
  nonreduced affine algebras, gives scheme-theoretic subgroup equality by Yoneda.
- V→Q, u↦un₀B, is an isomorphism onto an open dense subscheme: `D`, `d`,
  `eD : V.X ≅ D`, with d an open immersion of dense range and with
  `eD.hom ≫ d` equal to the displayed multiplication followed by π.
- Finite translate open cover: `m : ℕ`, rational points `a : Fin m → G(F)`,
  chart objects `D`, open immersions `d`, and isomorphisms `eD : ∀ k, V.X ≅ D k`.
  The displayed equation is precisely u↦a_k u n₀ B; its image is the translate
  of the preceding cell. The last universal condition says these images cover Q.
  Composing eD with the affine-space isomorphism gives the demanded A^N charts.
- Section and trivial right B-torsor on each chart: `s k ≫ π = d k`, and
  `IsPullback` with the map `(x,b) ↦ s_k(x)b` and projection to x asserts
  that D_k×B is isomorphic to G×_Q D_k by right multiplication. Its right
  B-equivariance follows from the group associativity diagram, so no unrelated
  non-equivariant product is substituted for the torsor trivialization.

Dependency declarations read and used:

- Mathlib `Field`, Algebra/Field/Defs.lean:180, and `IsAlgClosed`,
  FieldTheory/IsAlgClosed/Basic.lean:62; the latter's polynomial-splitting
  definition has its documented equivalence with existence of roots.
- Mathlib `CategoryTheory.GrpObj`, `Grp`, and `GrpObj.Hom.group` from
  CategoryTheory/Monoidal/Grp and the cartesian group-object interface;
  the group-scheme node's source `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`
  was read, including its subgroup definition and kernel conventions.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure`: full docstring and
  signature read. The theorem supplies exactly the predicates, action,
  positive-root characterization, radical and quotient data used above.
- Its imported `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`,
  `IsBorelGroupScheme`, `MultiplicativeType.splitTorus`,
  `SolvableGroupStructure.IsUnipotent`, and `TorusCharacterTangent.weightSpace`
  are reused; no second definition of any of them is introduced.
- Mathlib `AlgebraicGeometry.GeometricallyIntegral`,
  AlgebraicGeometry/Geometrically/Integral.lean:40; full definition and its
  irreducible/reduced equivalence read.
- Existing landed node `def-sfb-rank-one-root-interfaces` is added to stmt_deps,
  using `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `RankOneRoots.Character`, `pointImage`, `normalizer`, `torusInNormalizer`,
  `torusInNormalizer_normal`, and `Weyl`. The definitions and docstrings were
  read in full. This adds no new node and changes no existing dependency record.

The available recorded proof dependencies are imported privately: rank-one
reflections, root-subgroup parametrizations, homogeneous quotient geometry,
polynomial dimension, spectrum topology, proper/smooth base change and smooth
composition (already visible through the public Borel-pair import), finite-type
Jacobson spaces, closed-point residue fields, and regular/connected integrality.
The remaining proof dependencies have no Lean record yet and therefore have no
import to add. They are all named in the eight-step proof docstring.

Edge cases checked before writing and on rereading:

- Trivial group and a torus: Φplus is empty, N=0, W is trivial, V=1,
  Q=Spec F, the single C_w is G=B=T, and one chart suffices.
- SL₂ with upper-triangular B: W has two elements, V=A¹, the longest
  stratum is the open double coset and Q=P¹ has the expected affine charts.
- Characteristic two: characters, not their differentials, define roots and
  their inverses. No characteristic or root-system-rank restriction is present.
- Arbitrary central torus factors: no spanning assumption on roots is imposed.
- Nonreduced test schemes: subgroup equality and all maps retain them. The
  algebraically closed field tests are used only for the stratification clause.
- Empty cover index: permitted syntactically, as usual, but the conclusion
  `∀ x : Q.left, ∃ k, ...` excludes it when Q is nonempty; there is no extra
  nonempty-cover hypothesis. Universes are explicit and autoImplicit is disabled.

Searches performed (actual tool results):

1. msearch leanfinder: "Bruhat decomposition split reductive algebraic group
   longest Weyl element open big cell affine flag variety charts". Eight hits:
   root-pairing Weyl-group and representation results, plus unrelated action and
   measure results; none states scheme Bruhat decomposition or flag charts.
2. msearch loogle: "RootPairing, Subscheme, IsLocallyClosedImmersion".
   Zero hits; service reports unknown identifier Subscheme. Not an exact match.
3. msearch grep: "Bruhat|bruhat|longest.*[Ww]eyl|[Bb]ig[Cc]ell".
   One unrelated module-lattice comment about the Bruhat--Tits tree.
4. msearch leansearch: "Bruhat decomposition flag variety open big cell Weyl
   group". Eight hits on abstract RootPairing Weyl groups and Coxeter descent;
   none on algebraic-group Bruhat cells or their scheme charts.
5. rg in lean/WeilConjectures and lean/Sheaf for Bruhat, bruhat, bigCell,
   longest.*Weyl, weylGroup: no exact statement. The broader BorelPair search
   found RhoSectionModules.IsRhoBorelPair, which only describes Borel pair data.
6. grep -rn for the exact node id in lean/WeilConjectures: no hit.
7. rg of dag/lean_names_upstream.json for the node id and Bruhat/longest cell:
   no declaration match. DAG and project searches found the already landed
   RankOneRootInterfaces notions, which are reused directly.

No statement correction, disputed statement, dependency repair, or new node.
The item's statement and accepted proof split remain unchanged; only `lean` and
one added landed definition dependency change.

Compilation: scompile.py compiled both sandbox and library-mode forms with exit
code 0 (33.9 s and 7.6 s respectively); no errors or unexpected warnings.

## Second reading by Q56

Performed as a separate rereading pass in this same worker session: the dispatch
brief expressly forbids starting other agents. This does not claim an independent
peer review; the maintainer supplies that independent reading after delivery.

I reopened the original node and the final Lean file and checked each input
and output against the mapping above. The radical hypothesis is its maximality
property, not an arbitrary unipotent subgroup; Φplus is pinned to the conjugation
weights of Lie(B); the quotient has its actual right B kernel pair. The Weyl
quotient is the actual normalizer quotient and its character action has the
inverse in the required place. The uniqueness clause compares the images of
all positive roots, rather than merely testing a single regular weight.

I checked the multiplication equations factor through the declared inclusions,
the longest-stratum and flag-cell density assertions apply to different schemes,
and the arbitrary representative n₀ is quantified separately from the selected n.
IsIso(v w₀) is precisely equality over V of the immersed subschemes. The cover
maps are translates of the same un₀B chart and carry sections and the correct
right-multiplication pullback squares. Both geometric-integrality conclusions
are included. No clause is restricted to rational points: the subgroup equality
uses every test scheme, the cell parametrizations are over-F scheme isomorphisms,
and the partition explicitly includes algebraically closed extensions.

No mismatch was found on this rereading. There are no new or repaired dependency
modules to reread. The source's possible confusing big-cell terminology does not
change this statement: it consistently uses the specified V n₀ B cell and its
translates, rather than equating it with a differently based opposite cell.
