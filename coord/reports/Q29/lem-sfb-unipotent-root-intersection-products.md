## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.UnipotentRootIntersectionProducts
states AlgebraicGeometry.unipotent_root_intersection_products, with one sorry
and no new definitions. The item's mathematical statement and all fields other
than lean are unchanged. No dependency repair or new node was needed.

Read the node and its eight proof steps; all five statement-dependency nodes,
their recorded interfaces and source declarations; the Borel root coordinate
module; and Milne iAG2017, 21.66--21.69 (printed pp.444--446), 21.76--21.79
(pp.448--449), including formula (136). These identify scheme intersections,
not intersections of reduced subgroups. The current blueprint/latest chapter
has no duplicate Borel/root intersection statement. There is no repair note for
this item. The old CompactObject example is withdrawn; its node now points to
WeilConjectures.CategoryTheory.CompactObject, whose actual module was also read.

Hypotheses and clauses, individually:

- F algebraically closed: `{F : Type u} [Field F] [IsAlgClosed F]`.
- G is a reductive F-group scheme: `G : Grp (Over (Spec (.of F)))` and
  `hG : ReductiveTorusCentralizer.IsReductive G`. This is the dependency's
  existing smooth, connected, affine finite-type reductive predicate.
- Split maximal torus T: `iT`, `hT : IsMaximalTorus iT`, and `hsplit`.
  The rank may be zero. These are the Borel-pair theorem's exact binders.
- B and B' are Borels containing that SAME torus: `iB`, `hB`, `iB'`, `hB'`,
  and `j`, `hj : j ≫ iB = iT`, `j'`, `hj' : j' ≫ iB' = iT`.
- V and V' are the unipotent radicals: `iV`, `iV'`, `hV`, `hV'`.
  Each conjunction says closed, normal, smooth, connected, unipotent, and
  contains every smooth connected normal unipotent closed subgroup. This
  reproduces the maximality interface of reductive_borel_pair_structure.
- The positive roots are actual character weights, not differentiated
  characters: `aG`, `aB`, `aB'`, and `haG`, `haB`, `haB'` identify the three
  actions with conjugation through the same inclusions. `hαpos` says that the
  image of α is exactly the nontrivial weights of G occurring in BOTH B and B'.
  This is precisely S = Φ+ intersect Ψ+ under the Borel-pair theorem's
  characterization. `r`, `α : Fin r → ...`, and `hαinj` allow any ordering,
  without repetitions, including the empty ordering.
- The U_alpha are the root subgroups supplied by the root-parametrization
  dependency: `R`, `iR`, and `hR` say each is closed, smooth, connected,
  T-stable, with tangent image equal to the alpha weight space. This is its
  exact uniqueness characterization, so these are arbitrary presentations
  of those root subgroups, rather than a new construction or stronger input.
- The contextual quotient Q and right torsor π are `Q`, `π`, `hQproper`,
  `hQfinite`, `hπflat`, `hπsurj`, `hπinv`, and `hπtorsor`, exactly as in the
  Borel-pair theorem: proper finite type, flat surjective, invariant under
  right multiplication, with G times B identified as its kernel pair.
  W and its action serve only to describe the context; neither occurs in
  any assertion here, so no normalizer representative is chosen or needed.
  Characters are the dependency's actual group-scheme character Hom group.
- B intersect B' is `pullback iB.hom.hom iB'.hom.hom` in Over Spec F.
  The first two conjuncts say its structure map is Smooth and its underlying
  space is ConnectedSpace (including nonemptiness).
- V intersect B' is `pullback (iV ≫ iB).hom.hom iB'.hom.hom`.
  The next two conjuncts say smooth and connected.
- V intersect V' is
  `pullback (iV ≫ iB).hom.hom (iV' ≫ iB').hom.hom`.
  The next two conjuncts say smooth and connected.
- Equality V intersect B' = V intersect V' is `∃ e : ... ≅ ...` with
  `e.hom ≫ pullback.fst _ _ = pullback.fst _ _`. This is equality of closed
  subobjects of V, expressed independently of their pullback presentations;
  it is not merely an abstract isomorphism.
- First displayed multiplication isomorphism: `∃ mV`, `IsIso mV`.
  Its composite through V into G is the ordered List.ofFn product of the
  root inclusions composed with product projections. This equation determines
  the map uniquely, since the intersection's inclusion in G is a monomorphism.
- Second displayed multiplication isomorphism: `∃ mB`, `IsIso mB`.
  The source is the product of root factors tensor T.X, the Cartesian product
  over F. Its composite into G is the same ordered product, followed by the
  torus factor in that order (the Hom group multiplication `*`). This again
  pins the actual multiplication morphism, not an arbitrary isomorphism.
- Empty products: `r = 0 → Nonempty ((∏ᶜ ...) ≅ Over.mk (𝟙 (Spec (.of F))))`.
  The second conjunct supplies `eT : T.X ≅ B intersect B'` whose composite
  into G is iT, so the conclusion is equality with T as a closed subobject.
  The first product isomorphism then also makes the radical intersections
  trivial. The empty List product is the identity section.
- Persistence under algebraically closed extensions: the final universal
  quantification over `E`, `[Field E] [Algebra F E] [IsAlgClosed E]` says all
  three base-changed intersections are smooth and connected. The functor is
  the actual `Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F E)))`.
  Applying it to e and to the mV/mB isomorphisms transports their equalities
  and isomorphism properties automatically. As a right adjoint it preserves
  the finite products and pullbacks, hence these transported maps ARE the
  ordered multiplication maps of the base-changed subgroup intersections.
  This includes the empty product and the equality with the base-changed T.
  All schemes and extension fields use one arbitrary ambient universe, as
  in the recorded group-scheme scalar-extension API; there is no finiteness
  restriction on the extension.

Recorded dependency declarations used:

- Mathlib.Algebra.Field.Defs: Field (line 180), the field dependency's match.
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed (line 62), with the
  algebraic-closure node's explicitly recorded match for algebraic closedness.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj and Grp,
  the def-sc-group-scheme interface. The concrete group-scheme interpretation
  and IsClosedSubgroupScheme are in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure:
  AlgebraicGeometry.reductive_borel_pair_structure. Its public definitions
  supply ReductiveTorusCentralizer.IsReductive, IsMaximalTorus,
  MultiplicativeType.splitTorus, IsBorelGroupScheme, and weightSpace.
- Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations:
  AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations.
  The hR characterization is read directly from its signature and docstring.
- Sheaf.AlgebraicGeometry.GroupScheme.BorelRootProductCoordinates:
  AlgebraicGeometry.borel_root_product_coordinates, imported for the proof plan.
- Remaining recorded proof dependencies are imported from
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion (IsClosedImmersion),
  Sheaf.AlgebraicGeometry.StandardGroupSchemes (additive/multiplicative),
  Mathlib.AlgebraicGeometry.Morphisms.Smooth (Smooth), and
  Mathlib.Topology.Connected.Basic (ConnectedSpace).
  lem-sfb-regular-cocharacter-borel-description currently has neither a Lean
  record nor a Mathlib match, so there is no module to import for that proof-only
  dependency. The docstring preserves its exact role for stage 3.

Edge cases checked before writing: G = T and the trivial group (r = 0);
B' = B (all positive roots occur); opposite Borels in SL2 (no common positive
root, intersection T), also in characteristic 2; non-opposite Borels in SL3
(with a proper nonempty common positive root set); arbitrary order of the
common roots; and nonreduced test algebras F[epsilon]/epsilon². Pullbacks,
rather than point sets or reductions, retain the latter's infinitesimal data.
Smoothness and connectedness are conclusions, never assumed for intersections.
No source or statement fault, and no STATEMENT-DISPUTED flag.

Searches actually made:

1. msearch.py leanfinder, query "Scheme theoretic intersections of Borel
   subgroups containing the same maximal torus are smooth connected products
   of common positive root subgroups": eight hits in abstract root systems
   and Lie algebra theory, including RootPairing.GeckConstruction.cartanSubalgebra',
   LieAlgebra.rootSpaceProduct_def, and
   LieAlgebra.cartan_sup_iSup_rootSpace_eq_top. None states the group-scheme
   intersection assertion.
2. msearch.py loogle, query "IsBorelGroupScheme, IsReductive": zero hits;
   Loogle reports unknown identifier IsBorelGroupScheme (a project notion).
3. msearch.py grep, query "Borel|borel|root.*subgroup", subdirectory
   AlgebraicGeometry: zero Mathlib hits.
4. rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json,
   query "unipotent_root_intersection|root.*intersection|intersection.*root|
   lem-sfb-unipotent-root-intersection-products": only unrelated Lie/root
   tower text and references in BruhatLongestCellCharts, no declaration of
   this statement. A separate grep -rn for the literal item id in
   lean/WeilConjectures and a root-subgroup/Borel search in its GroupScheme
   directory had no matches. The sibling BorelRootProductCoordinates gives
   the full Borel radical product, not these intersections.

Compilation: prescribed scompile.py, against current server sources, succeeded
(exit 0, 6.7 s server compile of the final file). The local compiler had a disk-space error, and
the wrapper's normal server fallback succeeded. No Lean errors or unexpected
warnings were reported. The only proof is the required sorry.

## Second reading by Q29

A second pass by the same dispatched worker compared the final signature with
the node clause by clause (the independent review is the maintainer's).
Both radicals have the identical maximality characterization from the dependency;
both Borel inclusions contain the very same iT. The common root enumeration is
an equivalence condition, so neither extra factors nor missing roots are allowed.
The products use ordered multiplication, and the equations identify each map
inside G. In particular, the torus factor is on the right in mB. The isomorphism
e is over V, and eT is over G, so neither weakens a subgroup equality to an
abstract scheme isomorphism. All three smoothness/connectedness pairs are present
both over F and after extension. The empty-product clause includes r = 0
explicitly. The second pass made the contextual quotient and its right torsor explicit
as binders, matching the dependency signature; no statement correction was
needed. All variables and the universe are explicitly bound with autoImplicit false;
no file-local notation, private declaration, or local instance is used.

Delivery validation: the first deliver2.py --no-push run stopped at a local
disk-space failure. The prescribed retry used the normal server fallback and
returned OK: commit 2a378327f59 passes preflight and compiles. No launcher tool
was modified, and the shared repository was only read directly.
