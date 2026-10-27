## What changed

The proof uses the specified module pullback throughout. Additivity follows from its adjunction. A unit-compatible presentation by the actual abelian inverse image proves finite-limit preservation when the structural ring adjunct is invertible. The existing Sheaf.Paper.SignedLinePullbackExistence theorem supplies the normalized signed family; tensor recursion and evaluation transfer give uniqueness and isomorphism/scalar naturality. The ordinary binary tensor comparison is constructed with its pure-section formula. Signed line powers are flat on their rank-one charts. Flat-factor resolving normalization and localization then supply the unbounded derived action.

The original data declarations have moved, with the same fully qualified names, to the publicly re-exported SignedLineDerivedBaseChangeData module. The definition repair names the termwise complex tensor functor, gives DerivedActionData named projections for the same three comparisons, factors the three ordinary pure-section formulas and the action square/uniqueness clauses, and specializes generic one-constructor localization predicates to define DerivedLineConstraints and DerivedFamilyCoherence with exactly the previous witnesses and equations. The change record is coord/changes/signed-line-derived-data.md. No file under lean/WeilConjectures is changed. No target signature is changed.

## Proved and sorry left

The original hole is `SheafOfModules.SignedLineDerivedBaseChange.signed_line_derived_base_change` (one original hole). Its combining proof is complete. Its auxiliary existence, uniqueness, naturality, inverse-image presentations, finite-limit preservation, ordinary tensor comparison, signed-power flatness, flat-factor resolving normalization, derived comparison, and ordinary constraint theorems have complete Lean proofs.

Closed: `SheafOfModules.SignedLineDerivedBaseChange.signed_line_derived_base_change`, the item's one original `sorry`. Added: zero `sorry`; no unfinished statements are split off. Before this return repair, the complete 19-module packet passed `lcompile.py --all` with no warnings. Localized coherence compiled in 36.9 seconds, the ordinary tensor comparison in 41.0 seconds, the derived action in 9.6 seconds, and the original theorem in 12.4 seconds. The generic predicate repair preserves all the original witnesses and equations. After a subsequent fresh compile exceeded the time gate, the generic localization proof was simplified to lift its six constraints directly; this complete version compiled in 37.7 seconds. The retained 20 new DAG nodes describe proved component results and explicit data, not new holes. Two unchanged full-consumer checks exceeded 60 seconds without a type error; a check of the prefix containing its uses of this item also exceeded the limit. The exact `signedComparison_exists` consumer argument was then recompiled separately against the repaired interface, using its existing private helper API and local instances; it passed in 12.9 seconds. This checks the original theorem eliminations, `pull`, `derivedLine`, and `b.2.2`. The consumer source is not changed or delivered. A fresh build against the current tensor-power implementation exposed a conversion-sensitive rewrite in positive naturality; the two rewrites now explicitly allow definitional conversion, and naturality compiled in 37.4 seconds. The subsequent full check compiled coherence and naturality but timed out on the tensor comparison. Its local instance priorities now agree with the repaired data module, preventing alternative preadditive and zero-morphism instances from being unfolded during conversion.

## No longer needed

Return C-60622 (606221785): removed the unlanded duplicate module
`Sheaf.Algebra.Homology.SignedLinePullbackExistence` and its proposed node
`lem-pur-signed-line-pullback-existence` from this delivery. The item now imports
`Sheaf.Paper.SignedLinePullbackExistence` and applies its existing stronger theorem
`exists_signedLinePullbackNormalized _hcover a P Q _hP t`, owned by
`lem-pur-normalized-signed-line-pullback-exists`. No landed file or node is deleted.

No Lean module is withdrawn. The original item's public imports are preserved through its publicly imported data module; new proof imports are private. An unused proof import of ScalarHomOrdinaryTensorComparison was removed from SignedLineOrdinaryConstraints after its proof compiled without it.

The original DAG proof dependencies below are replaced by the explicit constructions in this delivery. This is removal from this proof route, not a claim that any source-library declaration can be deleted:

- `lem-sp-invertible-tensor-scalar-extension`.
- `lem-weil-pbc-exact-functor-derived-functor`.
- `lem-weil-pbc-independent-bounded-flat-kflat`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-sfb-ringed-derived-monoidal-comparisons`.

The derived action is obtained by exact termwise localization, so the general total-left-derived pullback theorem and its monoidal comparisons are not needed here. The flat-single normalization theorem gives the representative-normalized flat factor directly. Scalar naturality uses the already stated signed scalar/pullback square and its dual-local comparison. BoundedFlatIndependentCoefficients remains in a transitive import closure and is not claimed as a globally pruned module. The following four modules are absent from this item's actual import closure:

- `Sheaf.Paper.InvertibleTensorScalarExtension`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.

This is pruning from this proof's import route; no claim is made that unrelated library users have disappeared.

The obsolete top-level tool approvals removed from the item node are: `lem-sp-invertible-tensor-scalar-extension`, `lem-weil-pbc-exact-functor-derived-functor`, `lem-weil-pbc-independent-bounded-flat-kflat`, `lem-sfb-ringed-derived-monoidal-comparisons`. No approval is added or reordered.

## Where the brief, the DAG or earlier work was wrong

Return C-60622 repairs: the previous packet duplicated the existing public name
`SheafOfModules.exists_signedLinePullbackNormalized`. Its proposed module and node
are removed, and step 2 and proof_deps cite the existing owner. The item stmt_deps
now includes `def-pur-signed-line-derived-action-data`, which owns the relocated
statement data. The repair changes no theorem signature and keeps the rest of the
returned packet unchanged. There are now 18 Lean modules and 20 new nodes. The repaired item compiled
without warnings in 16.1 seconds (lcompile result 803e88e9b67dc4a7a18cce7d).
The launcher owner has corrected deliver3.py to preserve stmt_deps updates even
when the statement is unchanged. This resolves the tool limitation that blocked
the repaired packet. No launcher script or unrelated statement was changed by
this worker.

The same-universe inverse-image action helpers do not directly apply when the site object and morphism universes differ. The new SignedLine pullback construction helpers retain their argument and proof in the needed coefficient universe, without changing the adopted source tree. The defining pure-tensor comparisons must be kept opaque while using their section APIs; unfolding those constructions can exceed the single-file compile limit.

The original large normalization predicate is expensive to unify during witness construction. The definition repair keeps its exact mathematical content while giving it a constructor interface. The consumer audit found CartesianCoefficientTwists as the actual external user of the main theorem, the relocated pull and derivedLine, and the three comparison projections; the other hits of the short names were unrelated namespaces. Its unchanged source was compiled against the repaired interface, reaching the time gate without a type error; no consumer proof or statement was changed.


The earlier repair dry run `45027187324` compiled and passed preflight but omitted
the requested stmt_deps update, so nothing was pushed. The launcher correction
is now present. The repaired item was recompiled without warnings in 13.8 seconds
against the current environment before delivery.

## New nodes

`def-pur-signed-line-derived-action-data`: For the sheaf module categories and signed powers [def-pur-signed-line-pullback-normalization-data], define F to be the specified module pullback. Define signed isomorphism maps by positive tensor powers and precomposition with inverse powers for negative indices. Define D_L as the published unbounded derived tensor with L[0], and collapse as the total-complex single-factor comparison. ResolvingNormalization requires the comparison Q D_L ≅ (- tensor L) Q to agree with representativeIso followed by collapse on every K-flat representative. DerivedActionData consists of these comparisons on both sites and an isomorphism D_L D(F) ≅ D(F) D_M. DerivedAction requires flatness and the specified resolving normalizations, the termwise tensor comparison square, and uniqueness. DerivedLineConstraints specifies ordinary unit, positive reassociation and dual evaluation on all pure sections and specifies their derived lifts after Q. DerivedFamilyCoherence requires the same derived action family to commute with those three constraints on all derived objects. IsoNaturality and ScalarNaturality are the commuting signed-power squares for compatible line isomorphisms and arbitrary compatible extensions of coefficient rings. All definitions are the explicit formulas of the Lean attachment; no existence witness is used as definition data.

`def-pur-signed-line-module-inverse-image-action`: For a structural ring map a:R→U_*S and an R-module sheaf M, InverseImageAction is an S-action on the actual abelian sheaf inverse image of M, with semilinear restrictions and with eta(rm)=a(r)eta(m). It gives an S-module sheaf by retaining that same additive sheaf and those operations. Its underlying abelian sheaf comparison with the constructed abelian inverse image is the identity.

`def-pur-signed-line-ordinary-constraint-data`: Let A be a commutative ring sheaf, P an A-module sheaf, and P^[d] its signed powers [def-pur-signed-line-pullback-normalization-data]. OrdinaryLineConstraints(A,P,u,p,e) means: u: (- tensor P^[0]) ≅ Id sends x tensor r to r x; p_n: ((- tensor P^[n+1]) tensor P) ≅ (- tensor P^[n+2]) sends (x tensor y) tensor q to x tensor (y tensor q); and e_n: ((- tensor Hom(P^[n+1],A)) tensor P^[n+1]) → Id sends (x tensor phi) tensor y to phi(y)x. These identities hold on sections over every site object, for every module sheaf and every n≥0.

`def-pur-signed-line-pullback-unit-presentation`: For a continuous functor U:C→D, set inverse image L and its adjunction unit eta, a unit presentation of a sheaf T on D by a sheaf S on C is a morphism j:S→U_*T and an isomorphism i:T≅L(S) such that i(j(x))=eta(x) on every section. The canonical presentation of L(S) has unit eta and identity isomorphism.

`lem-pur-flat-line-resolving-normalization`: For a flat sheaf L on a ringed site, its single complex L[0] is K-flat and total tensor with it preserves quasi-isomorphisms. There exists a comparison c:Q⋙D_L≅(- tensor L)^complex⋙Q satisfying ResolvingNormalization [def-pur-signed-line-derived-action-data]: its value on every K-flat representative is the published representative comparison followed by the total-complex collapse.

`lem-pur-flat-tensor-derived-action`: Let F be an additive exact functor between the two module-sheaf categories, L and M flat fixed sheaves, and gamma:(- tensor L)⋙F≅F⋙(- tensor M). Then there exists b:DerivedActionData(F,L,M) satisfying DerivedAction(F,L,M,gamma,b) [def-pur-signed-line-derived-action-data]. Thus its resolving comparisons have the prescribed representative normalization and its derived comparison is the unique natural isomorphism whose square on every localized complex is the termwise image of gamma.

`lem-pur-identified-ring-pullback-finite-limits`: Let U:C→D preserve finite limits and coverings and let a:R→U_*S have invertible adjunct for a ring inverse-image adjunction. The specified module pullback F has unit-compatible presentations identifying S with the set inverse image of R and identifying its underlying abelian and set sheaves with the respective inverse images. Consequently F preserves finite limits. Coefficients lie in any universe containing the site object and morphism universes.

`lem-pur-signed-line-algebraic-pullback`: Let F be the specified module pullback for a:R→U_*S. Given compatible unit presentations identifying S with the set inverse image of R and identifying the underlying sets of F with the set inverse image, there exists an AlgebraicInverseImage whose module functor is F, whose ring-underlying comparison is the inverse ring presentation, and whose module-underlying comparison is the given one. Its additive and scalar operation comparisons satisfy the defining graph equations. All fields are constructed from these presentations.

`lem-pur-signed-line-derived-action`: Under the finite-limit, covering, invertible-ring-adjunct and local rank-one hypotheses of lem-pur-signed-line-derived-base-change, for every normalized signed family T there are pure-section-normalized ordinary tensor comparisons gamma_d and derived data b_d satisfying DerivedAction for each degree and DerivedFamilyCoherence simultaneously [def-pur-signed-line-derived-action-data]. The exact pullback instances are the supplied ones; the input complexes are unrestricted unbounded complexes.

`lem-pur-signed-line-localized-coherence`: Let F be an exact module pullback, T a normalized signed family [def-pur-signed-line-pullback-normalization-data], gamma_d its ordinary tensor comparison with the prescribed pure-section formula, and b_d a family satisfying DerivedAction(F,P^[d],Q^[d],gamma_d,b_d) [def-pur-signed-line-derived-action-data]. Then DerivedFamilyCoherence(F,P,Q,b) holds: the same eta family commutes with normalized derived right unitors, positive-power products and negative-positive evaluations on every unbounded derived object.

`lem-pur-signed-line-module-action-presentations`: Let U:C→D be continuous and its set inverse image preserve finite limits. Given a unit presentation [def-pur-signed-line-pullback-unit-presentation] of S by R whose unit is a:R→U_*S, and an isomorphism presenting the underlying set of the abelian inverse image compatibly with its unit, there is an InverseImageAction(a,M) [def-pur-signed-line-module-inverse-image-action] on that abelian inverse image. The action is obtained by transporting scalar multiplication along inverse image and the given presentations; its module axioms and restriction semilinearity hold globally.

`lem-pur-signed-line-module-inverse-image-adjunction`: Under the ring and underlying-set unit presentations of lem-pur-signed-line-module-action-presentations, the specified module pullback has a natural isomorphism, after forgetting to abelian sheaves, with the constructed abelian inverse image of the underlying module. The isomorphism carries the module pullback adjunction unit to the abelian inverse-image unit. No equality of site object and morphism universes is required.

`lem-pur-signed-line-ordinary-constraints`: For any module sheaf P over a commutative ring sheaf A, there exist the ordinary unit, positive-power reassociation isomorphisms and negative-positive evaluation transformations satisfying OrdinaryLineConstraints(A,P) [def-pur-signed-line-ordinary-constraint-data]. They are natural in the module tensored on the left and have exactly the unit, reassociation and contraction pure-section formulas of that definition.

`lem-pur-signed-line-power-flat`: If P is locally free of rank one on a covering of the final object of its ringed site, then every signed power P^[d], d∈Z [def-pur-signed-line-pullback-normalization-data], is flat in the sense of IsFlatOnSite [def-pc-flat-sheaf-modules], including the degree-zero unit and the internal duals of positive powers.

`lem-pur-signed-line-pullback-naturality`: For rank-one P,Q and a normalized family T [def-pur-signed-line-pullback-normalization-data], the family commutes with every compatible pair of line isomorphisms and with arbitrary compatible extensions R→R′ and S→S′ of coefficient rings. In negative degrees the isomorphism maps are inverse precomposition on internal Hom. The scalar squares use the specified signed scalar comparisons and impose no flatness condition on either ring map.

`lem-pur-signed-line-pullback-tensor`: Let U preserve finite limits and coverings, let the adjunct of a:R→U_*S be invertible, and fix an isomorphism t:F(L)≅N of module sheaves. There exists a natural isomorphism gamma:(- tensor L)⋙F≅F⋙(- tensor N). On every source pure section x tensor y inserted by the pullback unit, gamma is the pure tensor of the inserted x and t applied to the inserted y. No flatness or rank assumption on L is needed.

`lem-pur-signed-line-pullback-unique`: For any ringed-site module pullback F, an isomorphism t:F(P)≅Q, and two signed-power isomorphism families T and T′, if both satisfy SignedLinePullbackNormalized [def-pur-signed-line-pullback-normalization-data], then T=T′. The conclusion requires no rank-one hypothesis beyond the existence of the normalized families.

`lem-pur-signed-line-pullback-unit-presentation`: Given unit presentations (S,T,j,i) and (S′,T′,j′,i′) [def-pur-signed-line-pullback-unit-presentation], maps T→Z agree if they agree on j(x) for every source section. A source map a:S→S′ transports to i;L(a);i′^{-1}:T→T′ and sends j(x) to j′(a(x)). If L preserves finite products, presentations tensor to a presentation of the Cartesian product, whose comparison is (i×i′) followed by the inverse product comparison.

`lem-pur-signed-line-sheaf-pullback-forget`: Let U:C→D be continuous and V:E→Set a forgetful functor. Suppose left Kan extensions along U^op exist, V preserves them, and target sheafification exists and is preserved by V. Then the constructed E-valued sheaf inverse image followed by V is naturally isomorphic to the set inverse image of the underlying sheaf. This comparison sends the underlying E-valued adjunction unit to the set-valued adjunction unit. The site object and morphism universes may differ; the set universe contains both.

`lem-pur-signed-line-unit-presentation-graphs`: Let p,q,r be unit presentations [def-pur-signed-line-pullback-unit-presentation]. Suppose a binary operation on their target sheaves agrees on unit sections with a source operation. For any sheaf Z and source sections x:Z→S, y:Z→S′, z:Z→S″ satisfying z=op(x,y), their transported maps from L(Z) satisfy the corresponding target operation equation. Likewise a target constant agreeing with the source constant on units carries every source constant graph to that target constant graph.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
