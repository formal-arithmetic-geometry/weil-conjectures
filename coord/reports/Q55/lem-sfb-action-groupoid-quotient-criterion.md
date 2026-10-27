## Worker report

The delivery states `AlgebraicGeometry.SchemeAction.actionGroupoid_quotient_criterion`
in `Sheaf.AlgebraicGeometry.ActionGroupoidQuotientCriterion`. It adds the definition
node `def-sfb-etale-scheme-action-torsor-groupoid` and its module
`Sheaf.AlgebraicGeometry.EtaleSchemeActionTorsorGroupoid`. No mathematical statement
of the item changes; its only changes are `lean` and the added definition dependency.
All theorem proofs are `sorry`. Every definition has concrete data.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. Test schemes are arbitrary `Over S`.
  The independent fibre universes are `v,w` on `BasedCategory.{v,w}`; no equality
  between these and the scheme universe is imposed.
- The finite abstract group is `H : Type u` with `[Group H] [Finite H]`.
  `G : Over S`, `[GrpObj G]`, and `incl : H → (Over.mk (𝟙 S) ⟶ G)` with
  `hincl : IsColimit (Cofan.mk G incl)` present exactly the coproduct of copies
  of S indexed by H. `hincl_one` and `hincl_mul` specify the multiplication
  induced by H. Thus G is H_S with its specified component labels, not an
  arbitrary finite group scheme. Giving a coproduct cocone rather than choosing
  Mathlib's coproduct does not change the group scheme or add a hypothesis.
  Base change gives H_T at every T. Finite groups can be represented in the
  scheme universe, as allowed by the node's size convention.
- The S-scheme U and its left action are `(G U : Over S) [ModObj G U]`.
  An action of this constant scheme is precisely an action of H by S-automorphisms.
  No freeness, smoothness, finite-type assumption, or characteristic restriction
  on U or S is introduced.
- The target stack is `Z` with `hZ : IsModuliStack Z`, exactly the recorded
  total-category convention of `def-sfb-stable-pointed-moduli-groupoids`.
  Its definition includes fibred groupoids and étale object and arrow descent.
  Algebraic-space representability of Z is not assumed: that statement dependency
  supplies conventions, rather than an additional algebraicity hypothesis.
- `A : BasedFunctor (actionGroupoid G U) Z` bundles a and alpha. Restrict A to
  `schemeToActionGroupoid G U` to recover a. On a vertical arrow with label h,
  A gives alpha(h,u). The category's composition label is gh, so A's functor laws
  give alpha(1,u)=id and alpha(g,hu) alpha(h,u)=alpha(gh,u). Basedness gives the
  stated compatibility with arbitrary test-scheme maps; arrows in fibred
  groupoids are cartesian, so this is pullback compatibility. Conversely the
  stated coherent atlas data define this functor; nonconstant group sections
  are glued on their clopen components using the target's isomorphism sheaves.
- `hlift` says that for each actual target object z there is an étale covering
  sieve R of its base. For every b:W→base(z) in R, there are an action object x
  and r:A(x)→z lying over b. `Z.p.IsHomLift b r` requires the bases to be W and
  base(z); in a CFG this arrow is exactly an isomorphism from A(x) to z|W.
  Covering sieves express existence of the node's jointly surjective étale
  family and all its refinements. No chosen cleavage or pullback is added.
- `hrel` gives full faithfulness of `moduliFiberMap A T` for every T. For each
  u,v over T, this is exactly a bijection from the labels h with hu=v to all
  isomorphisms a(u)→a(v). Those labels are scheme maps T→G, not just globally
  constant elements of H. Since representable source fibres are discrete,
  this is precisely equivalence of the node's discrete relation scheme with
  the fibre of U×_Z U; it neither quotients nor forgets target automorphisms.
- `[U/H]` is `etaleTorsorGroupoid G U`. Its objects are genuine schemes P,T,
  actions, invariant projections, and equivariant maps P→U. The extra predicate
  `IsEtaleLocallyTrivial` is exactly the displayed local equivariant product
  trivialization. The underlying fppf triviality proof is redundant because
  every étale covering family is fppf; proof irrelevance ensures that it creates
  no new objects or arrows. As a full subcategory it uses precisely the original
  equivariant cartesian arrows preserving P→U. Over an identity, cartesianness
  means these are equivariant T-isomorphisms, as in the node. Restriction of
  torsors is the actual fibre product already encoded in these cartesian arrows.
- The canonical atlas-and-arrows functor is `etaleTrivialTorsorFunctor G U`.
  Its underlying objects and maps reuse `trivialObject` and
  `trivialTorsorFunctor`, including the required R(h inverse) convention.
- The existential C is the required canonical extension. D and the two
  isomorphisms `C.comp D ≅ id` and `D.comp C ≅ id` give an equivalence over
  the base, including the inverse and vertical unit/counit. The comparison
  `ε : q.comp C ≅ A` is on the entire action groupoid, so it prescribes both
  atlas objects and alpha arrows, rather than only the object map.
- For any C' and its prescribed comparison ε', the unique isomorphism eComp
  satisfies `(q ◁ eComp.hom) ≫ ε'.hom = ε.hom`, expressed using
  `BasedCategory.whiskerLeft`. This is exactly the unique compatible
  2-isomorphism claimed in the final sentence, not uniqueness of an arbitrary
  unmarked equivalence of stacks.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  its jointly-surjective-cover topology is `Scheme.etaleTopology.over S`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsModuliStack`, and `moduliFiberMap`;
  also read the signatures/docstrings for discreteModuli and the two-fibre product.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and its site conventions, inherited through the recorded moduli module.
- `Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids`:
  `ActionObject`, `ActionHom`, `actionGroupoid`, `TorsorObject`, `TorsorHom`,
  `torsorGroupoid`, `trivialObject`, and `trivialTorsorFunctor`. These are reused,
  not copied. Their complete signatures and construction laws were read.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `CategoryTheory.Pseudofunctor.exists_groupoid_stackification_local_description`
  is imported as a proof dependency. Its coherent-pullback formulation can be
  applied to the CFG via choices of cartesian lifts at proof time.
- The other two theorem proof dependencies,
  `lem-sfb-stack-fully-faithful-local-equivalence` and
  `lem-sfb-finite-constant-torsor-map-etale-stack`, currently have no Lean record.
  Their statements were read. No declaration from them is needed to type this
  theorem; they remain steps in its postponed proof rather than assumptions.
- `def-weil-size-convention` is a convention, with no module to import.

Sources read: local Stacks `examples-stacks.tex`, Proposition 04WM and its actual
trivial-torsor and inverse-right-translation formulas; `algebraic.tex`, Lemmas
04T4 and 04T5. Their algebraicity/smoothness hypotheses are not smuggled into the
agent-formulated local-lifting criterion, whose relation is an explicit hypothesis.

Edge cases checked before writing:

- The empty S, empty U, and empty test scheme are allowed. There is only one
  morphism from the empty scheme to G: the relation never incorrectly requires
  a unique globally constant H-label on an empty scheme. Covering sieves allow
  empty covers where the étale topology does.
- H=1 reduces to the usual descent recognition of a representable stack.
  H itself cannot be empty because it is a group.
- A nonfree action and stabilizer automorphisms are retained by fibre groupoids.
- Disconnected test schemes admit nonconstant sections of H_T, since labels
  are arbitrary maps to the coproduct scheme, not elements of H.
- Nontrivial torsors are retained: only étale local triviality is imposed,
  and no global section or global trivialization is required.
- No invertibility of |H| is needed; a finite constant group scheme is étale
  even when the characteristic divides |H|. No noetherian or base-field condition.
- For the new trivial-object theorem, the maximal sieve and product square
  work over any S and any G, including the empty scheme.

Searches for the item (msearch.py, recorded in searches.jsonl):

- LeanFinder: “A stack presented by a finite group action is equivalent to its
  quotient stack of equivariant scheme torsors”: 8 unrelated finite-action and
  Galois-category hits, no quotient-stack criterion.
- Loogle `"QuotientStack"`: 0 hits.
- Mathlib grep `QuotientStack|ActionGroupoid|quotient_stack`: 2 hits in
  FreeGroup/NielsenSchreier, concerning set action groupoids.
- Project rg found SchemeActionTorsorGroupoids and ActionGroupoidTorsorComparison.
  The latter assumes a base field, smooth affine group, and fppf stackification;
  it does not give this arbitrary-base étale-stack criterion.
- The upstream constant-group-scheme declaration was read; it requires an
  AddCommGroup, so it cannot represent an arbitrary noncommutative finite H.
  The theorem therefore uses the coproduct universal property directly, with
  the actual unit and multiplication equations, without making a second
  constant-group-scheme definition.
- rg of the item id under lean/WeilConjectures returned no declaration.
- Additional LeanSearch, LeanFinder, Mathlib/project grep, DAG and blueprint
  searches for the new definition are recorded in its mathlib_searches and below.

Validation: both delivered modules compiled cleanly with the prescribed scompile.py
wrapper, separately in dependency order. No errors or additional warnings remain.
No STATEMENT-DISPUTED flag or statement correction is needed.

## New nodes

`def-sfb-etale-scheme-action-torsor-groupoid` defines the étale locally trivial
full subcategory of the existing scheme-torsor category, its based projection,
and the actual factorization of the specified trivial-torsor functor. Its named
proof obligation says the trivial object is étale locally trivial; the node's
statement and docstring give the maximal-sieve/product-square proof. The source
is Stacks 04WL/04WM with the étale local-triviality convention used in the item's
finite-constant torsor lemma. LeanSearch returned site and étale-morphism notions;
LeanFinder returned étale-site forgetful functors and the set action groupoid;
Mathlib and project grep found no `IsEtaleLocallyTrivial`, `etaleTorsorGroupoid`,
or `EtaleTorsorObject`. The broader project search found and reuses the fppf
scheme-torsor construction. DAG search found statements about these torsors but
no definition of the étale subcategory; blueprint_refs search "etale torsor"
found only H1/Picard comparisons. This is the missing étale specialization, with
no duplicate action, scheme, fppf torsor, or cartesian-arrow definitions.

## Second reading by Q55

I re-read the node, each signature, and both complete module files in a separate
pass in this session. The dispatcher explicitly forbids starting another agent;
this is a self-check, with the maintainer's independent review still to follow.
The comparisons checked were the finite group, arbitrary scheme base, coproduct
constant group scheme with the correct multiplication, arbitrary left action,
actual stack fibres, local lifting of every object, bijectivity on the complete
arrow relation, the scheme-torsor definition with étale trivializations, the
inverse-right-translation sign, existence of an inverse over the base, and
uniqueness of the compatible 2-isomorphism. All have the counterparts listed
above. In particular hrel is bijectivity for every pair of atlas objects, rather
than an equivalence of the whole action groupoid with Z(T), which would wrongly
force every torsor to be globally trivial. The uniqueness comparison is natural
on arrows as well as objects. No mathematical mismatch was found. Parser-only
binder names `ι` and `η`, reserved by scoped monoid notation, were changed to
`incl` and `eComp`. The new module reuses scheme torsors via a full subcategory;
its extra fppf local-triviality proof is logically redundant and introduces no
restriction. All construction data are explicit; only the named triviality law
and the assigned theorem are postponed.
