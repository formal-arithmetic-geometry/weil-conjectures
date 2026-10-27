## Worker report

Item: `lem-sfb-local-system-affine-descent-presentation`, group O4, stage 2.
Module: `Sheaf.Paper.LocalSystemAffineDescentPresentation`.
Main declaration:
`AlgebraicGeometry.Scheme.ProEt.localSystem_affine_descent_presentation`.

The module states the entire finite affine presentation, its natural representation,
and the clopen transition descent datum. The only postponed theorem is the main
statement, with proof `sorry`; its docstring contains all ten DAG proof steps.
All six helper definitions have actual data and source/blueprint docstrings.
One new definition node binds the existing clopen-decomposition declaration;
there are no dependency repairs or statement corrections.

Hypotheses, in the order of the node:

- A scheme X: `X : Scheme.{u}`.
- X quasi-compact: `[CompactSpace X]`.
- X quasi-separated: `[QuasiSeparatedSpace X]`.
- A set S in the fixed small universe: `S : Type u`, with no finiteness or
  nonemptiness assumption. Scheme coproducts indexed by S therefore exist in
  `Scheme.{u}`. `ULift.{u+1} S` represents exactly the same label set in the
  larger universe of sheaf values; it adds no mathematical hypothesis.
- F a sheaf of sets on the small pro-etale site:
  `F : Sheaf (Scheme.ProEt.topology X) (Type (u+1))`. Objects of `X.ProEt`
  have universe u+1 and morphisms universe u. No equality of those universes
  is imposed. The larger value universe implements the size convention.
- Supplied covering `{U_i -> X}`: `I : Type i`, `U : I -> X.ProEt`, with
  `hcover` membership of the underlying family in `proetalePrecoverage X`.
  Each `U k` already carries its weakly etale structure morphism.
- Supplied trivializations: `trivializations`, a natural isomorphism for each
  k between `(Scheme.proEtaleSetRestriction X (U k)).obj F` and
  `(constantSheaf (topology (U k).left) ...).obj (ULift S)`. The existing
  restriction functor is continuous precomposition by structure-map composition.
  Its maps and values are unchanged on underlying schemes; no local copy remains.

Conclusion clauses, in the order of the node:

- Finitely many affine pro-etale objects: `n : ℕ`, `A : Fin n -> X.ProEt`
  and `∀ j, IsAffine (A j).left`. In particular n may be zero.
- Each maps over X to an original member: `α : Fin n -> I` and
  `_refinement : ∀ j, A j ⟶ U (α j)`. These are genuine morphisms in
  `X.ProEt`, with the over-X triangle built into their type.
- Their coproduct V and its map p: `V : X.ProEt`, inclusions `ι`, the
  equations `ι j ≫ V.hom = (A j).hom`, and
  `Nonempty (IsColimit (Cofan.mk V.left ι))`. This is the actual scheme
  coproduct universal property, without choosing a particular isomorphic
  representative of the coproduct. The structure map p is `V.hom`.
- V affine: `IsAffine V.left`.
- p weakly etale: part of `V : X.ProEt`, explicitly `V.prop`.
- p flat, surjective and quasi-compact: `Flat V.hom`, `Surjective V.hom`,
  `QuasiCompact V.hom`.
- Both singleton coverings: `Presieve.singleton V.hom` is in
  `fpqcPrecoverage X` and in `proetalePrecoverage X`, separately.
- The trivialization psi on V: the existential sheaf isomorphism `ψ`,
  from `(Scheme.proEtaleSetRestriction X V).obj F` to the constant sheaf.
- T = coproduct over s of V: `localSystemCopies V.left S` is the object
  `Over.mk (Sigma.desc (fun _ : S => 𝟙 V.left))`; its underlying scheme is
  Mathlib's actual coproduct `∐ fun _ : S => V.left`.
- For every weakly etale W over V the two natural bijections: the underlying natural
  isomorphism of the sheaf isomorphism `ψ` is the first, and `e` is the second, landing in
  `localSystemCopiesHom V.left S`. The latter is the relative Yoneda
  functor, restricted along `ProEt.forget`, followed by the fully faithful
  `uliftFunctor`. Its value is `ULift (Over.mk W.hom ⟶ T)`, canonically
  equivalent to the ordinary Hom set. No arbitrary comparison map occurs.
  Natural isomorphisms of Type-valued functors give the required natural
  bijections on every W and their naturality on every morphism.
- Constant labels go to component sections: the equation involving
  `e.hom.app`, `toSheafify`, and `ULift.up (localSystemLabel S W.hom s)`.
  The label map is the concrete arrow `W.hom ≫ Sigma.ι ... s`.
- The represented functor is a sheaf: the separate
  `Presheaf.IsSheaf (topology V.left) (localSystemCopiesHom V.left S)` clause.
- Sections are exactly S-indexed clopen decompositions: for every W and
  relative map a, its component preimages satisfy the existing
  `IsClopenDecomposition`; for every such decomposition P there is a
  unique relative map a with those preimages. Thus both directions and
  uniqueness are stated. The displayed component restriction equation
  describes the actual morphism on each piece. `IsClopenDecomposition`
  means pairwise disjoint open pieces with supremum top; each complement
  is the union of the other pieces and is open, so each piece is closed.
- R and its projections: the genuine scheme `pullback V.hom V.hom` with
  `pullback.fst` and `pullback.snd`.
- A scheme descent datum on T: `D : Over.DescentDatum V.hom T`, the
  dependency's recorded definition, not a new substitute. This is the
  transport presentation of a scheme descent datum, with transport on
  every test scheme and the ordinary identity, naturality and cocycle laws.
- D realizes the transition between the two restrictions of psi: the HEq
  identity for `ψ.inv.hom.app` after `e.inv.app`, and `D.transport`. It says transporting
  a represented point does not change the section of F. The two resulting
  sections have the same underlying scheme and equal structure arrows
  to X by h. HEq expresses equality under precisely that identification,
  with no arbitrary section bijection. Both maps f1 and f2 are weakly
  etale, as required for evaluating the restricted sheaves; D itself is
  a scheme descent datum on all schemes, not merely on this subcategory.
- A unique R-isomorphism delta: `∃! δ` between the two actual
  `(Over.pullback p_a).obj T`. `LocalSystemTransitionRealizes` specifies its
  action on every relative point, via Mathlib's fixed map-pullback
  adjunction and the transport D. This characterizes its underlying
  scheme map by Yoneda. In particular it is not a bare existence of an
  arbitrary isomorphism.
- The inverse realizes the inverse transition: the second
  `LocalSystemTransitionRealizes` clause uses the reversed projections,
  `pullback.condition.symm`, and `δ.symm`.
- For each source label s the target labels partition R into clopen pieces:
  `LocalSystemTransitionClopen S D p1 p2 pullback.condition`.
  Its pieces are the inverse images of the actual target component opens
  under `D.transport p1 p2 ... (localSystemLabel S p1 s)`.
- The component map is the identity on the indicated piece, from source
  component s to target component t: the equation in
  `LocalSystemTransitionClopen` is precisely the component inclusion
  composed with that piece's inclusion into R. Via the realization
  property of delta this describes the actual pullback-scheme morphism.
  The coproduct universal property and the clopen cover determine the
  assembled map. The reversed clopen clause records the inverse assembly.
- Cocycle on the triple fibre product: this is exactly the field
  `Over.DescentDatum.transport_transport` of D. For any triple of maps
  with equal composites to X it asserts transport23(transport12(a)) =
  transport13(a). Apply it to the projections of V×_X V×_X V; the
  realization property characterizes the pulled-back delta maps, so
  this is delta23 composed with delta12 equals delta13. This uses the
  recorded dependency's transport encoding of the same scheme cocycle;
  it does not replace the cocycle by a per-point existence assertion.
- Empty X and empty S: neither is excluded by a binder or a positivity
  condition on n. All empty-case meanings are retained by the existing
  coproduct, sheaf, and descent-datum definitions.

Dependencies used (module and declaration):

- `def-weil-pbc-scheme-conventions`: a convention record; uses Mathlib's
  `Scheme`, `IsAffine`, `CompactSpace`, `QuasiSeparatedSpace`, `Flat`,
  `Surjective`, and `QuasiCompact`, with
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `def-weil-size-convention`: convention only, expressed by universe u,
  the u+1 site object/value universes and the fully faithful ULift.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, recorded
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the set-sheaf component
  is its existing Mathlib `Sheaf`/`Presheaf.IsSheaf`, as its record specifies.
- `def-weil-pbc-proetale-site`:
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`,
  `ProEt.topology`, `Scheme.proetalePrecoverage`.
- `def-weil-pbc-constant-sheaf`:
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `constantSheaf`.
- `def-weil-pbc-fpqc-covering`:
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`, `Scheme.fpqcPrecoverage`
  (publicly included by the site module).
- `lem-weil-pbc-scheme-coproduct-family`:
  `Mathlib.AlgebraicGeometry.Limits`, scheme coproduct instance,
  `Sigma.ι`, `Sigma.desc`, `Cofan.mk`, `IsColimit`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `pullback`,
  `pullback.fst`, `pullback.snd` (publicly included by scheme limits).
- `def-pd-descent-datum`:
  `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`,
  `CategoryTheory.Over.DescentDatum`, especially its `transport` and
  `transport_transport` fields. `Over.pullback` and
  `Over.mapPullbackAdj` come from its public Mathlib imports.
- `def-sfb-clopen-decomposition` (new node, existing declaration):
  `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`,
  `AlgebraicGeometry.IsClopenDecomposition`. Only this plain definition is
  a statement dependency. The theorem
  `AlgebraicGeometry.coproductCopiesMorphismsClopen` remains a proof input,
  through `lem-galois-coproduct-copies-morphisms-clopen` in proof_deps.
- `def-a1-proetale-set-restriction` (already landed):
  `Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover`,
  `AlgebraicGeometry.Scheme.proEtaleSetRestriction`. This is the actual
  sheaf-valued restriction functor used in the hypothesis and in ψ.

The remaining recorded proof modules are imported privately:
`Sheaf.Paper.FiniteAffineProEtaleRefinement`
(`Scheme.finite_affine_proetale_refinement`),
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
(`ProEt.weaklyEtale_localization`),
`Sheaf.AlgebraicGeometry.EtaleComparison`
(`etale_indEtale_weaklyEtale_comparison`),
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`
(`CategoryTheory.sheafification_sections_local`), and
`Mathlib.CategoryTheory.Sites.LocallyBijective` (locally bijective
sheafification recognition). The other Mathlib proof dependencies are
already included through scheme limits, the pro-etale site and morphism
modules: finite affine coproducts, source locality and base change of
weakly etale morphisms, affine open covers, qcqs permanence, fpqc
subcanonicity, Yoneda full faithfulness and sheafification. No proof
import is omitted for a cycle.

Edge cases checked before writing and again on second reading:

- Empty X: choose n=0, so A, alpha and refinement are empty functions;
  V is the empty scheme, an affine scheme. Its map to X is a singleton
  cover. The empty-cover sheaf condition gives a unique section on every
  object, and the empty coproduct universal property supplies V. No
  nonempty refinement lemma is invoked on this case.
- Empty I: covering forces X empty, and n=0 is permitted.
- Empty S over nonempty V: T is empty. Its relative Hom functor has no
  sections on nonempty W and one section on empty W, just as the initial
  sheaf; the empty indexed decomposition exists exactly on empty W.
  The overlap isomorphism is the unique empty-scheme isomorphism.
- Singleton S: T is canonically V and all transitions are identity.
- Infinite S: no claim that T is affine or quasi-compact. Only the finite
  family A has an affine coproduct. Target labels of a source label may
  vary on different clopen pieces, not a single global permutation.
- Non-quasi-compact W and nonaffine R: unrestricted. No affineness or
  compactness binder is imposed on these test schemes.

Searches for an existing statement and helper notions:

1. `msearch.py ... leanfinder "Locally constant sheaf pro etale finite
   affine cover coproduct scheme descent datum"`: eight hits, mainly
   affine-transition-limit cover constructions and one condensed
   locally constant colimit. None is this sheaf presentation theorem.
2. `msearch.py ... loogle "constantSheaf, Scheme.ProEt, Over.DescentDatum"`:
   service returned zero hits, unknown identifier `constantSheaf`.
   The actual Mathlib declaration was therefore read directly in
   `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`.
3. `msearch.py ... grep "constantSheaf|DescentDatum" AlgebraicGeometry/Sites`:
   one unrelated ElladicCohomology import. Local rg in Mathlib and both
   project roots found the dependency declarations used here, not the
   complete statement. `rg` for all eight proposed declaration names in
   Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` found no collision. Searching the node id
   in `lean/WeilConjectures` found no pre-existing statement.
4. Direct source reading: the latest blueprint proof (2), all recorded
   statement-dependency signatures and docstrings, and the existing
   coproduct-clopen, finite affine refinement, restriction/localization,
   constant-sheaf, fpqc and transport-descent interfaces. These supply
   every mathematical notion. The repair adds a definition node binding the
   existing clopen notion, which previously had only a theorem-node owner.

No STATEMENT-DISPUTED flag and no node fault. The original statement is
unchanged. The six remaining helper definitions name concrete expressions belonging
to this node's presentation; the existing restriction notion is reused.

Validation: prescribed `scompile.py O4 <item> <file>` passed both sandbox
and library module checks, initially in 2.7 s and 3.4 s respectively, with
no errors or warnings. All variables and universes are explicitly bound;
`set_option autoImplicit false` is set. No global build was run.

## Second reading by O4

The dispatcher explicitly prohibits starting other agents; this is a
fresh clause-by-clause rereading by the author, with the node and Lean
module open, not a claim of an independent worker review. The maintainer's
independent reading follows delivery, as specified in the task brief.

Checked all three paragraphs against the signature and expanded each of
the six helper definitions. The first paragraph retains the supplied
cover and trivializations without requiring any member to be affine,
quasi-compact or nonempty. The first existential paragraph retains each
finite chart, its over-X refinement map, the scheme coproduct universal
property, affineness, weak etaleness, flatness, surjectivity,
quasi-compactness and both covering predicates. The section comparison
paragraph has two natural isomorphisms, the exact constant-label unit
normalization, sheafhood, and existence and uniqueness for every clopen
decomposition. The last paragraph supplies the recorded full scheme
descent datum; the HEq compatibility identifies its transition with the
given F, the unique actual pullback-scheme isomorphism realizes it on all
points, the inverse realizes the inverse, and both component descriptions
are explicit. The dependency's cocycle field has exactly the required
23-after-12 orientation. No missed clause, additional hypothesis, hollow
construction, or smaller-universe restriction was found. The DAG adjustment
beyond lean is adding the new definition node
`def-sfb-clopen-decomposition` and the landed
`def-a1-proetale-set-restriction` to stmt_deps. The clopen theorem remains
in proof_deps and is absent from stmt_deps.


## New nodes

`def-sfb-clopen-decomposition` binds the existing declaration
`AlgebraicGeometry.IsClopenDecomposition` in
`Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen` with `existing: true`.
There is no new module and no copied definition. Source: current blueprint,
stratified-lattice scheme proof (2), its clopen label pieces; Stacks 03YW.
For `W : Scheme.{u}`, arbitrary `E : Type v` and `P : E → W.Opens`,
`∀ e e', e ≠ e' → Disjoint (P e) (P e')` renders pairwise disjointness,
and `(⨆ e, P e) = ⊤` renders the union being W. Openness is built into
`W.Opens`; complements are unions of other pieces, so the pieces are closed.
Empty pieces are permitted. For empty E the union equation holds exactly
when W is empty; for empty W every piece is empty, regardless of E. There
is no `Small` or finiteness hypothesis, nor any relation between u and v.

Searches on 2026-10-23: `msearch.py leansearch` and `leanfinder` queried
"A clopen decomposition of a scheme is a pairwise disjoint family of open
subsets whose union is the whole scheme" (eight hits each, related topology
and open-cover ingredients); `msearch.py grep` queried
`IsClopenDecomposition|Pairwise.*Disjoint` in Mathlib AlgebraicGeometry
(five hits in Limits, none defining this notion). The exact hit names are
recorded in the new node. `rg` in Mathlib, WeilConjectures and Sheaf found
the sole definition in CoproductCopiesMorphismsClopen; other project hits
are uses. A scan of definition nodes found no declaration binding or title
for this notion. `blueprint_refs.py search 'clopen decomposition'` returned
`0 blueprint nodes match 'clopen decomposition'`. Thus this delivery adds
only its missing DAG definition record, reusing the existing declaration.

## Returned delivery repaired

Compared the saved packet with the current read-only base: only lean and
stmt_deps of the item differ; its mathematical statement, proof and
proof_deps are unchanged. The initial saved-packet dry run passed at
383f5b8e18c, but the independent review defects still required these repairs:

- H2: removed `lem-galois-coproduct-copies-morphisms-clopen` from stmt_deps;
  added `def-sfb-clopen-decomposition`, whose existing:true record is the
  plain definition. The theorem remains in proof_deps unchanged.
- H4/H12: deleted `localSystemRestriction` and its lean.declarations entry.
  Imported the shared restriction module and added
  `def-a1-proetale-set-restriction` to stmt_deps. Both the supplied
  trivializations and ψ now use `(Scheme.proEtaleSetRestriction X _).obj F`.
  The compatibility expression evaluates `ψ.inv.hom.app` after `e.inv.app`;
  this is the same underlying presheaf map as before, using the canonical
  sheaf restriction. No hypothesis or conclusion changes.

Repair self-check: reread the node and complete signature after the edits.
All finite-cover, coproduct, naturality, constant-label, sheafhood, clopen,
transport, unique delta, inverse and cocycle clauses are retained. Rechecked
empty X, I and S, singleton and infinite S, and arbitrary test W. Read the
new node against the exact existing definition and its docstring; the
statement and all universes agree. No statement correction is needed.
Server scompile.py passed the revised module in 2.1 s (sandbox) and 2.2 s
(library), without errors or warnings. No other file is compiled or built.

The repair dry run required the current schema field `import_flags` on the
new definition node; it is the empty list (no import flags).
