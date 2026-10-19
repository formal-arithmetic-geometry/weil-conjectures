## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle` states the ambient ordinary
unbounded pro-etale support triangle for an arbitrary finite ring, including noncommutative rings.
Its single theorem `AlgebraicGeometry.ProEtale.exists_proEtale_closedSupportTriangle` has proof
`sorry`. The only supporting instance is structural zero-map preservation for the actual
sectionwise module pushforward; its field is definitionally `rfl`, with no postponed proof.
All six proof steps of the reviewed DAG node are included in the theorem's docstring.

The previous worker's blocker concerned stage-1 resplitting. This is a stage-2 statement
assignment: the current item is reviewed and split but has no Lean declaration. I preserved
its statement, proof, proof dependencies, status and review fields. I added only the Lean
record and the already-landed coefficient-map node to statement dependencies.

### Hypothesis and conclusion correspondence

- A scheme T: `{T Z U : Scheme.{u}}`, using the recorded small sites without identifying
  their object universe `u+1` with their morphism universe `u`.
- T Noetherian: `[IsLocallyNoetherian T] [CompactSpace T]`, exactly the two fields of
  Mathlib's `AlgebraicGeometry.IsNoetherian`. No finiteness or separation condition is added.
- Closed immersion: `(i : Z ⟶ T) [IsClosedImmersion i]`.
- Its open complement: `(j : U ⟶ T) [IsOpenImmersion j]` and
  `(hU : Set.range j = (Set.range i)ᶜ)`. In particular j need not be an arbitrarily chosen
  open subobject; the equality fixes the required complement. Quasi-compactness of j is
  a consequence of the Noetherian hypothesis and is not added as a hypothesis.
- Finite ring A: `(A : Type (u + 1)) [Ring A] [Finite A]`. The two topology classes specify
  the discrete topology required by the dependency's coefficient-sheaf construction; every
  ring has this topology, and there is no characteristic or nontriviality restriction.
- D(S_proet,A): `FiniteCoefficientDerivedCategory S A`, the existing ordinary localization
  of all cochain complexes in `FiniteCoefficientModules S A` over the recorded sheafified
  continuous-function ring. There is no use of the bounded or constructible subcategories.
- i_*: `iPush`, with a natural isomorphism from termwise application of
  `SheafOfModules.pushforward (finiteCoefficientDirectImageMap i A)` followed by the
  derived localization Q to `Q ⋙ iPush`. This is its exact descent to the ambient derived
  category. Both objects and morphisms are specified by this isomorphism, not by an
  arbitrary chosen functor or an arbitrary coefficient map. Localization makes this
  descent unique up to its unique compatible natural isomorphism.
- j^*: `jPull`, with the analogous natural isomorphism from the already recorded
  `finiteCoefficientModulePullback j A` applied termwise and localized. Exactness is the
  recorded `finiteCoefficientModulePullback_exact`. This uniquely specifies its descent.
- Ri^!: `iShriek` and `(closedAdj : iPush ⊣ iShriek)`. This is precisely the right adjoint
  on the entire ambient derived categories. The adjunction determines it up to its unique
  adjunction isomorphism, rather than choosing an object from a bare existence assertion.
- Rj_*: `jPush` and `(openAdj : jPull ⊣ jPush)`. Since j^* is the fixed exact sheaf inverse
  image, its right adjoint is the ordinary total right derived open direct image; on a
  K-injective complex it is the termwise direct image. This characterization avoids a
  redundant second construction and is valid also for noncommutative rings.
- Every K: `∀ K : FiniteCoefficientDerivedCategory T A`.
- First arrow i_*Ri^!K → K: `closedAdj.counit.app K`.
- Second arrow K → Rj_*j^*K: `openAdj.unit.app K`.
- Last arrow and shift: existential `δ : jPush.obj (jPull.obj K) ⟶
  (iPush.obj (iShriek.obj K))⟦(1 : ℤ)⟧`.
- Distinguished triangle: `Triangle.mk ... δ ∈ distTriang (FiniteCoefficientDerivedCategory T A)`.
- No constructibility of Ri^!K: there is no predicate on K or on `iShriek.obj K`.
  “In addition to the open–closed triangle” identifies the other localization triangle
  from the surrounding unit; the assertion here is the displayed closed-support triangle.

The two localization isomorphisms and the two adjunctions are existential witnesses for
canonical universal properties, not input hypotheses. They introduce no extra assumption.
They determine the functors up to the same isomorphisms implicit in writing derived
functors in the source. No definition is obtained by choosing arbitrary data from `sorry`.

### Dependency declarations and sources read

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; the ring-specialized category for
  commutative coefficients, and its underlying site convention. For the arbitrary ring in
  this node the recorded finite-coefficient specialization below is used.
- `Sheaf.Paper.RefinementCoefficientRealization` reexports
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, and `FiniteCoefficientDerivedCategory`. The primary theorem
  `finiteCoefficientRealization_full_faithful_essSurj` is commutative and is not needed
  to replace the already-defined arbitrary-ring category. Its full signature/docstring
  were read; the module containing the dependency record is imported unchanged.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory.standard`, and `DerivedCategory.Q`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `Triangulated`:
  `CategoryTheory.Pretriangulated`, `Triangle.mk`, `distTriang`, `IsTriangulated`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`,
  `proEtaleSheafDirectImage`, `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`;
  the actual functor uses the recorded small-site model and the standard fibre product.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`: `finiteCoefficientModulePullback`,
  `finiteCoefficientModulePullback_additive`, `finiteCoefficientModulePullback_exact`.
  The transported action is c_f inverse(r) times m and needs no commutativity.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`: `finiteCoefficientDirectImageMap`;
  the canonical map is precomposition on continuous functions followed by sheafification.
  This already-landed node is added to `stmt_deps`, as expressly permitted in the brief.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.pushforward`; its source shows that zero morphisms are preserved by rfl.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`, read in full and imported
  for the proof route; no resolution-existence hypothesis is placed on the theorem.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.

The recorded proof-dependency modules are imported where available. The legacy
`WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion` imports the legacy
UpperLowerStar definitions, duplicating the finite-coefficient definitions reached by
our statement dependencies; that proof-only import is omitted to preserve the published
finite-coefficient interface. The source declaration was read. Proof dependencies without
Lean records are not restated in this statement delivery; the theorem docstring names
all of them, and no missing proof-only statement is needed to type the statement.

### Source and edge cases

Read the blueprint source at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-localization/lem-exc-proetale-support-triangle.md`
from the launcher's read-only literature mirror, because the shared clone contains only
literature indexes. Its displayed formula, ambient category, finite-ring hypothesis,
K-injective short exact sequence, and explicit no-constructibility sentence agree with
the current reviewed DAG and this declaration.

Checked T empty; Z empty and j an isomorphism; i an isomorphism and U empty; the zero ring;
finite matrix rings (so noncommutativity is essential); K zero; unbounded K; nonreduced
closed subschemes; disconnected T; arbitrary open-complement presentation up to isomorphism.
No binder excludes any of these cases. In particular zero ring sheaves on the empty site
are not treated as having distinct constant scalars, and no condition `Nontrivial A` occurs.

### Searches

- `msearch.py leanfinder`: “closed immersion open complement pro-etale finite ring modules
  support distinguished triangle” returned eight algebraic etale-locus declarations;
  none states the node.
- `msearch.py loogle`: `Triangle.mk, Adjunction.counit, Functor.rightDerivedFunctor` returned
  no hits and reported unknown identifier `Triangle.mk` in the service index.
- `msearch.py leansearch`: “closed support localization distinguished triangle in derived
  category of pro etale module sheaves” returned generic triangleOfSES and localization
  triangle declarations; none includes the geometric support construction or its maps.
- `msearch.py grep`: `support.*triangle|supportTriangle|support_triangle` in
  `Mathlib/Algebra/Homology` returned zero matches.
- `rg` for the item id and support-triangle notions in the pinned WeilConjectures tree,
  the framework tree, and `lean/Sheaf` found
  `WeilConjectures.SixFunctors.ProEtale.Derived.Localization` in the framework. I read the
  full file. Its `exists_distTriang_derivedLowerStarClosedUpperShriekAdjunction_counit`
  requires `[CommRing R]`, so it cannot be an exact existing match for finite rings in
  this node. The other Sheaf support-triangle files concern other sites or categories.
- `scompile.py --source Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
  confirms that the current server's chosen direct-image API also still requires CommRing.
  The present theorem uses the existing canonical RingCat coefficient map and Mathlib's
  pushforward directly and characterizes the derived operations by universal properties;
  no recorded dependency is replaced and no second direct-image definition is introduced.

No statement correction, new node, or dependency-node repair is made.
No STATEMENT-DISPUTED issue remains. All direct writes are confined to this sandbox.

## Second reading by Q07

I independently read the shared node, the sandbox node and complete module, the
blueprint source `sec-smooth-purity/sk-prop-sf-localization/lem-exc-proetale-support-triangle.md`
and its surrounding unit in `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/`.
The node's source is a blueprint markdown lemma, not a Stacks tag with additional
standing hypotheses. Its own hypotheses are Noetherian T, a closed immersion, its open
complement, and a finite ring. The unit subsequently specializes to finite-type k-schemes
and constructible complexes; the lemma explicitly concerns the ambient category before
that restriction. I did not import those stronger unit hypotheses into the lemma.

Object, hypothesis and conclusion checklist (each verdict is a match):

1. **Schemes T, Z, U:** `{T Z U : Scheme.{u}}`; all three use the same small-site size
   convention. I read `Scheme.proEtaleBaseChange`, `proEtaleSheafDirectImage`, the inverse
   image and adjunction declarations, and the `proEtaleSiteModel` transport in
   `ProEtaleInverseImage.lean`. Objects have universe u+1 and morphisms universe u; the
   theorem imposes no equality between them.
2. **T Noetherian:** `[IsLocallyNoetherian T] [CompactSpace T]`. I checked Mathlib
   `Noetherian.lean`: `IsNoetherian` extends exactly these two classes. No separation,
   dimension or finite-type hypothesis is present. I also checked the recorded
   `pqf-def-locnoeth` and quasi-compact-scheme dependency signatures.
3. **Closed immersion i:** `(i : Z ⟶ T) [IsClosedImmersion i]`, using the dependency's
   Mathlib class, which extends surjectivity on stalks and records a closed embedding.
   Z is a scheme, not just a closed subset; nonreduced closed subschemes are retained.
4. **Open complement j:** `(j : U ⟶ T) [IsOpenImmersion j]` and
   `(hU : Set.range j = (Set.range i)ᶜ)`. This is exactly a presentation of the complement
   by an open immersion; it allows every isomorphic presentation of that open. No
   quasi-compactness assumption is added: it follows from T being Noetherian.
5. **Finite ring A:** `(A : Type (u + 1)) [Ring A] [Finite A]` with
   `[TopologicalSpace A] [DiscreteTopology A]`. The latter express precisely the discrete
   coefficient convention of `def-weil-pbc-proetale-modules`, not a ring restriction:
   every finite ring can carry the discrete topology. `Ring` admits the zero ring and
   noncommutative rings. The common coefficient universe is that of the dependency;
   any finite ring has a presentation there. No characteristic condition is introduced.
6. **Ambient D(S_proet,A):** `FiniteCoefficientDerivedCategory S A`. I opened the
   dependency module `RefinementCoefficientRealization` and its reexport
   `ProEtaleFiniteModules`, rather than relying on the name of its commutative main
   theorem. The actual arbitrary-`Ring` definitions are the sheafified presheaf
   `C(ConnectedComponents W, A)`, `ringedSiteModules`, and `DerivedCategory` with its
   standard localization. Thus these are all left module sheaves and all integer-indexed
   cochain complexes. I checked the abstract derived-category and triangulated-category
   dependencies against `DerivedCategory.Q`, `Triangle.mk` and `distTriang`. Neither a
   bounded subcategory nor the fixed-coefficient upstream presentation is substituted.
7. **Closed i_*:** the existential `iPush` is specified by the natural isomorphism
   between termwise `SheafOfModules.pushforward (finiteCoefficientDirectImageMap i A)`
   followed by Q, and `Q ⋙ iPush`. I read the canonical coefficient-map construction in
   `ProEtaleConstantRingMap`: extension by ring sheafification of precomposition along
   the fibre-product projection. The Mathlib pushforward uses exactly this map for the
   scalar action. Thus the statement specifies its action on all complexes and maps,
   not just objects or some arbitrary functor. The localization's universal property
   determines the descended functor up to compatible natural isomorphism.
8. **Open j^*:** `jPull` has the corresponding localization isomorphism for the recorded
   `finiteCoefficientModulePullback j A`. I read its body: inverse image on the small
   model followed by restriction of scalars along the inverse canonical coefficient
   isomorphism. I also read `finiteCoefficientModulePullback_exact`, whose finite-limit,
   finite-colimit and short-exact-sequence clauses concern this same functor for arbitrary
   rings. This gives the exact ordinary inverse image, with its transported action.
9. **Ambient Ri^!:** the existential `iShriek` and `closedAdj : iPush ⊣ iShriek` give
   precisely the right adjoint on the entire derived categories. **Ordinary Rj_*:**
   `jPush` and `openAdj : jPull ⊣ jPush` give the right adjoint of the exact open inverse
   image. This is the ordinary total right derived direct image, with no completed or
   constructible category. The right adjoints are specified by their adjunction universal
   properties. These are conclusions, not additional input assumptions; no data definition
   chooses an undetermined object out of a sorry existence proof.
10. **Quantification:** the functors and adjunctions are fixed before
    `∀ K : FiniteCoefficientDerivedCategory T A`, as in the source. They do not vary
    arbitrarily with K.
11. **First arrow i_*Ri^!K → K:** `closedAdj.counit.app K`. **Second arrow
    K → Rj_*j^*K:** `openAdj.unit.app K`. Both are the indicated adjunction maps.
12. **Connecting arrow and distinguishedness:** `∃ δ` has source
    `jPush.obj (jPull.obj K)` and target `(iPush.obj (iShriek.obj K))⟦(1 : ℤ)⟧`;
    `Triangle.mk (closedAdj.counit.app K) (openAdj.unit.app K) δ ∈ distTriang ...`
    gives every vertex, direction and the cohomological +1 shift of the displayed formula.
13. **No constructibility of Ri^!K:** neither K nor its image has any boundedness,
    constructibility, Tor-amplitude or completeness predicate. The phrase “in addition to
    the open–closed triangle” refers to the surrounding result; the assertion of this node
    is its displayed closed-support triangle, with no extra uniqueness/naturality clause.

Edge cases checked: T empty; Z empty with j an isomorphism; i an isomorphism with U empty;
K zero or unbounded; the zero ring; finite noncommutative matrix rings; disconnected schemes;
nonreduced closed subschemes. There is no index set or degree n in this theorem, and the
only degree is the integer shift +1. No nonemptiness, positive-characteristic exclusion,
nontriviality, affine, reduced or dimension bound excludes one of these cases. Universes
remain the dependency's scheme u / sheaf u+1 convention throughout.

Independent searches used different wording from the worker:

- `msearch.py ... leanfinder "right adjoint of a closed immersion direct image and open
  restriction unit distinguished localization triangle" returned eight hits, chiefly
  `Scheme.Modules.restrictAdjunction` and its unit/counit formulas. Those are Zariski
  O-module operations, not this pro-etale finite-ring triangle.
- `msearch.py ... loogle "DerivedCategory.triangleOfSES_distinguished" found the generic
  short-exact-complex triangle theorem. It provides the final categorical step but no
  geometric support functors or adjunction arrows.
- Independent `rg` on Mathlib's homology tree, the pinned upstream WeilConjectures tree,
  the exact shared framework and shared Sheaf tree for `closedUpperShriek`,
  `exists_distTriang`, `support_triangle` and `localizationTriangle` found the upstream
  `ProEtale.Derived.Localization` theorem. I opened its binders and conclusion: the ambient
  variable is `[CommRing R]`; its coefficients are fixed-ring `ModuleCat` sheaves. It is
  not an exact match for arbitrary finite rings. The adic/constructible siblings and
  Zariski support triangles likewise do not match. No exact existing declaration was found.

There are no new nodes, dependency modules or statement corrections to review. The only
added statement dependency is the already published canonical coefficient-map node, which
is directly used by the signature. I verified that the source and DAG statement are
unchanged and `lean.statement` is verbatim the theorem signature. All six DAG proof steps
are carried in the theorem docstring, including the noncommutative restriction-of-scalars
argument. Both declarations have source/blueprint docstrings and all lines fit 100 columns.
The supporting zero-map instance contains only definitional structural data (`rfl`), not a
new mathematical theorem; the sole theorem proof is `sorry`. No hollow definition, private
copy, unbound universe/variable, or statement mismatch was found. Accordingly I changed
no Lean or DAG text; this second reading adds the independent audit and validation only.

Validation: `scompile.py Q07 lem-exc-proetale-support-triangle
lean/Sheaf/AlgebraicGeometry/ProEtaleClosedSupportTriangle.lean` succeeded locally with
both its sandbox check and library-module check, with no errors or warnings.
