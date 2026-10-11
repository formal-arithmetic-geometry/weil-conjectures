## Worker report

The module `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison` states two theorems,
with only `by sorry` proofs. No definitions, new nodes, or dependency replacement modules
are needed. The two declarations together render the item's complete statement.

Source read: `/home/ubuntu/c1-stacks-review/more-algebra.tex`, section-tor-independence,
equation-comparison-map (lines 14901–14941), and
`/home/ubuntu/c1-stacks-review/perfect.tex`, proof of
lemma-single-complex-base-change-condition, Tag 0DJ8 (lines 6475–6529).
These are available local copies of the cited Stacks sources; the repository's
`literature/stacks-project/` checkout is absent on this machine.

Hypotheses and clauses:

- R -> A and R -> R': `(R A B : Type u) [CommRing R] [CommRing A] [CommRing B]`
  with `[Algebra R A] [Algebra R B]`. B is R'. An Algebra structure is exactly the
  commutative-ring map in the node. No flatness, boundedness, finiteness, or
  Tor-independence hypothesis is imposed.
- A' is literally `A ⊗[R] B`. Complexes are unbounded
  `CochainComplex (ModuleCat.{u} A) ℤ`, including the zero complex.
  Shared universe u accommodates rings in any universes by taking their maximum.
  `[HasDerivedCategory.{w} (ModuleCat.{u} B)]` in the first theorem is the choice
  of localization category/morphism universe, not a mathematical restriction.
- The canonical comparison in D(R') is the unique natural transformation `c`
  from `sourceComplex R A B ⋙ DerivedCategory.Q` to
  `targetComplex R A B ⋙ DerivedCategory.Q`. The spanLeft IsIso clause and the
  equation `whiskerRight spanLeft Q ≫ c = whiskerRight spanRight Q` specify it.
  Those existing models are respectively R-flat resolution followed by extension,
  and A-flat resolution followed by restriction and extension. Termwise tensor
  associativity identifies B tensor_R P with P tensor_A (A tensor_R B).
- The first theorem's final universal clause takes arbitrary P -> M and E -> P,
  with `QuasiIso p`, `QuasiIso e`, and the ordinary-module `kFlat` predicates
  over A and R. The isomorphisms `es,et` are fixed by the two augmentation
  equations, rather than assumed arbitrary identifications. The final equation
  `es.hom ≫ c.app M = Q.map ((extend R B).map e) ≫ et.hom` is exactly the
  E tensor_R B -> P tensor_A A' representative required by the node.
- For every i: `∀ i : ℤ` in the first theorem and `(i : ℤ)` in the second.
  `homologyFunctorFactors` in the first theorem identifies H^i(c) with the
  already defined `comparison R A B i`, joining the two statements.
- The tensor-algebra-module structures are the lifted functors `S,T` to
  `ModuleCat (A ⊗[R] B)`. `eS,eT` identify their restrictions along includeRight
  with the existing B-module cohomology functors `source,target`. They are
  natural B-linear isomorphisms, so the existing B-action is preserved.
- The first two equations in the second theorem fix the A-action on both lifts:
  includeLeft a acts as `source.map (a • 𝟙 M)` or `target.map (a • 𝟙 M)` under
  eS/eT. Multiplication by a on M represents the multiplication endomorphism in
  D(A), restricted to D(R) and extended to D(B). Thus this is the node's specified
  action, not an arbitrary module structure. Commutation with B and agreement
  of the two R-actions are built into being a module over the tensor algebra.
  On the target these equations characterize the evident P tensor_A A' action.
- A'-linearity of H^i(c): `c : S ⟶ T` has A'-linear components by its type.
  The equation after the two action equations identifies its restriction with
  the canonical `comparison` under eS,eT. Naturality is part of NatTrans.
- Every prime q': `q' : PrimeSpectrum (A ⊗[R] B)`. Its q,p',p are exactly
  the comaps along `algebraMap A (A ⊗[R] B)`, includeRight, and
  `algebraMap R (A ⊗[R] B)`, respectively.
- `Rp,Aq,Bp,D` are arbitrary ring models of the four localizations, expressed
  by four `IsLocalization.AtPrime` binders. The Algebra and IsScalarTower binders
  express the canonical induced maps, with `_hB` fixing the otherwise ambiguous
  right-factor map B -> D. These are not extra geometric assumptions: all four
  standard prime localizations have these structures by localization's universal
  property. Quantifying over models avoids privately defining duplicate local rings.
- The local tensor ring is literally `Aq ⊗[Rp] Bp`. `f` is its canonical map to D,
  characterized by `_hfA,_hfB` on the two inclusions. These imply the value on
  every pure tensor and hence specify f uniquely. Local lifts `Sl,Tl`, their
  identifications `eSl,eTl`, their action equations and `cl` express the same
  derived tensors and comparison over Rp,Aq,Bp.
- First localization identity: `alpha` is a natural D-linear isomorphism
  `S ⋙ extendScalars (algebraMap A' D) ≅
    extend A Aq ⋙ Sl ⋙ extendScalars f`.
  Its component at M is H^i(M tensor-derived_R B) tensor_A' D =
  H^i(M_q tensor-derived_Rp Bp) tensor_(Aq tensor_Rp Bp) D.
- Second localization identity: `beta` identifies the localized target T
  with the localized local target Tl. The final natural isomorphism (the type
  inside `Nonempty`) identifies `Tl ⋙ extendScalars f` with
  `resolution Aq ⋙ extend Aq D ⋙ homologyFunctor D (.up ℤ) i`.
  Composing beta with its whiskering by `extend A Aq` gives precisely
  H^i(M tensor-derived_A A') tensor_A' D = H^i(M_q tensor-derived_Aq D).
  This is a natural isomorphism of functors, not independent isomorphisms of
  individual cohomology objects.
- Compatibility: the displayed equation involving `alpha.hom,beta.hom` is the
  commuting square between `whiskerRight c (extendScalars (A' -> D))` and
  `whiskerLeft (extend A Aq) (whiskerRight cl (extendScalars f))`. Under the final
  target identification it is the exact localized comparison of the node.
  Left-sided tensors from ModuleCat.extendScalars are the right-sided tensors
  in the node via the canonical symmetry for commutative rings.

Dependency declarations inspected and reused:

- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `DerivedCategory.Q`, `HasDerivedCategory`; and HomologySequence,
  `DerivedCategory.homologyFunctor`, `homologyFunctorFactors`.
- `def-pc-module-kflat-complex`:
  WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat,
  `CategoryTheory.MorphismProperty.kFlat`, specialized to
  `HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)`; its equivalent module criterion
  is exposed in FromJoel.CategoryTheory.Abelian.Flat.KFlat.
- `def-pc-ring-tensor-cohomology`: Sheaf.Algebra.Homology.RingTensorCohomology,
  `resolution`, `augmentation`, `restrict`, `extend`, `sourceComplex`, `targetComplex`,
  `middleComplex`, `spanLeft`, `spanRight`, `source`, `target`, `comparison`.
  The entire source module and its defining docstrings were read.
- Original dependencies were read in full: Sheaf.AlgebraicGeometry.DerivedCategory,
  `AlgebraicGeometry.schemeDerivedCategory` and its quasi-coherent subcategory;
  Sheaf.Algebra.Homology.KFlat, `CochainComplex.IsKFlat`/`IsKFlatResolution`.
  Those are sheaf-specific, hence the citation correction below. No private
  replacement of either notion was made.

Edge cases checked before writing: zero rings are allowed (then PrimeSpectrum is
empty, so the localization clause is vacuous but the comparison/action clauses remain);
zero and arbitrary unbounded complexes; all positive, negative and zero cohomological
degrees; non-flat ring maps, specifically R=k[t], A=B=k with t acting by zero
(the comparison need not be an isomorphism, and the statement does not assert one);
identity base change and identity localizations. No localization of the R-complex at
A' is used: only its cohomology lift S is extended over A'.

Searches made before writing:

- msearch.py leanfinder: `canonical derived tensor base change comparison and localization
  of cohomology`; eight hits on Tor functors and cotangent homology localization,
  no matching derived-complex statement.
- msearch.py loogle: `DerivedCategory, TensorProduct`; zero hits.
- msearch.py leansearch: `derived tensor base change comparison map localization cohomology`;
  unavailable, Internal Server Error (recorded as unavailable, not a negative result).
- msearch.py grep: `derivedTensor|tensorDerived|baseChangeComparison`, Mathlib/Algebra;
  zero hits.
- Direct rg of `lem-pc-affine-derived-base-change-comparison-map` in
  /home/ubuntu/weil-src-slopmaster2/WeilConjectures and the corresponding name fragments
  in dag/lean_names_upstream.json: no declaration.
- Direct rg of derived tensor, tensor localization, comparison-map and base-change
  patterns in WeilConjectures and lean/Sheaf: found the existing ring tensor cohomology,
  BaseDerivedTensorCohomologyModel, MixedTotalTensor, fixed-second-factor functor,
  flat-second-localization and balanced/associator modules; read these candidates.
  RingTensorCohomology provides the required canonical models and is reused.
  None supplies both the two prime-localization identities and their comparison square.
- Exact full-name collision search for both new theorem names in Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no matches.

Validation: server scompile.py compiled the complete 185-line module cleanly in 2.8 s.
Both proofs are sorry and all universes and variables are explicitly bound, with
`set_option autoImplicit false`. No mathematical statement is disputed.

## Statement corrected

Old statement, verbatim (also preserved in `statement_change.old_statement`):

Let R\to A and R\to R' be ring maps and put A'=A\otimes_R R'. For a complex M^\bullet of A-modules [def-pc-derived-category] there is a canonical comparison morphism c:M^\bullet\otimes_R^{\mathbf L}R'\to M^\bullet\otimes_A^{\mathbf L}A' in D(R') (Stacks, More on Algebra, equation comparison-map): it is E^\bullet\otimes_R R'\to P^\bullet\otimes_A A' for a K-flat complex P^\bullet of A-modules representing M^\bullet and a quasi-isomorphism E^\bullet\to P^\bullet from a K-flat complex E^\bullet of R-modules [def-pc-kflat-complex]. For every i, H^i(M^\bullet\otimes_A^{\mathbf L}A') has its evident A'-module structure, while H^i(M^\bullet\otimes_R^{\mathbf L}R') is an A'-module as follows: a in A acts by H^i(a\otimes_R^{\mathbf L}\operatorname{id}_{R'}) through End_{D(A)}(M^\bullet)\to End_{D(R)}(M^\bullet)\to End_{D(R')}(M^\bullet\otimes_R^{\mathbf L}R'), and this action commutes with R', hence combines to an A'=A\otimes_R R' action. With these structures H^i(c) is A'-linear. For every prime \mathfrak q' of A', with images \mathfrak q of A and \mathfrak p',\mathfrak p of R',R, there are natural isomorphisms H^i(M^\bullet\otimes_R^{\mathbf L}R')\otimes_{A'}A'_{\mathfrak q'}\cong H^i(M^\bullet_{\mathfrak q}\otimes^{\mathbf L}_{R_{\mathfrak p}}R'_{\mathfrak p'})\otimes_{A_{\mathfrak q}\otimes_{R_{\mathfrak p}}R'_{\mathfrak p'}}A'_{\mathfrak q'} and H^i(M^\bullet\otimes_A^{\mathbf L}A')\otimes_{A'}A'_{\mathfrak q'}\cong H^i(M^\bullet_{\mathfrak q}\otimes^{\mathbf L}_{A_{\mathfrak q}}A'_{\mathfrak q'}), under which H^i(c)\otimes_{A'}A'_{\mathfrak q'} is the map induced by the comparison morphism for R_{\mathfrak p}\to A_{\mathfrak q}, R_{\mathfrak p}\to R'_{\mathfrak p'} followed by scalar extension along A_{\mathfrak q}\otimes_{R_{\mathfrak p}}R'_{\mathfrak p'}\to A'_{\mathfrak q'}.

Its mathematical text is unchanged. The two inaccurate type-level citations
were corrected: `[def-pc-derived-category]` -> `[def-weil-abstract-derived-category]`,
and `[def-pc-kflat-complex]` -> `[def-pc-module-kflat-complex]`.
A citation `[def-pc-ring-tensor-cohomology]` now identifies the existing canonical
comparison models. The original sheaf declarations cannot be applied to ModuleCat
complexes; the existing ordinary-module declarations are precisely the objects
used by Stacks equation-comparison-map and the affine proof of Tag 0DJ8.
This is not a correction to a blueprint unit's statement. No hypothesis, conclusion,
proof step, or proof dependency is changed. Only statement citations and their
stmt_deps change, with old_stmt_deps recorded.

Every node whose stmt_deps or proof_deps cites this item was found by searching all DAG
node JSON files and then checking those two arrays (matches only in blueprint.from,
created, and searches were excluded). There is exactly one actual citer:

- `lem-pc-rf-single-complex-affine-base-change`: holds true. Its proof uses the same
  comparison, A'-linearity, two localization identities, and compatibility. The correction
  only points the ring-module notions to their actual definitions, so all uses still hold.
  The citer is not edited.

Dry run: deliver2.py --no-push printed OK; the server compile and maintainer preflight
passed except for the independent second-reading section, which the tool explicitly
reserves for the second reader. Nothing was pushed.

## Second reading by C1

I independently read the corrected node first against More on Algebra,
section-tor-independence, equation-comparison-map (local more-algebra.tex,
14901–14941), and perfect.tex, lemma-single-complex-base-change-condition,
Tag 0DJ8 (6475–6529), including the surrounding hypotheses. The affine
calculation requires commutative rings and arbitrary unbounded module complexes;
the scheme and quasi-coherence hypotheses are used to reach that calculation,
not extra hypotheses on its rings or complexes. I then read the complete
185-line delivered module and its dependency declarations.

Object/hypothesis/conclusion checklist (all verdicts: matches):

1. Ring maps R -> A and R -> R': `R A B : Type u`, three `CommRing`
   instances and `Algebra R A`, `Algebra R B`; B denotes R'. No flatness,
   Tor-independence, Noetherian, characteristic or boundedness hypothesis.
2. A' = A tensor_R R': literally `A ⊗[R] B`, throughout the second theorem.
3. Arbitrary A-complex M: `CochainComplex (ModuleCat.{u} A) ℤ`, the domain
   of `sourceComplex`, `targetComplex`, `S` and `T`. The two underlying
   functors are respectively `restrict R A ⋙ resolution R ⋙ extend R B`
   and `resolution A ⋙ restrict R A ⋙ extend R B`, read in
   `Sheaf.Algebra.Homology.RingTensorCohomology`. Tensor associativity
   identifies the latter with the A-derived tensor with A'.
4. Comparison in D(R'): `exists_affineDerivedBaseChangeComparison` asserts
   `IsIso (whiskerRight spanLeft Q)` and a unique natural transformation c
   satisfying `whiskerRight spanLeft Q ≫ c = whiskerRight spanRight Q`.
   Thus the left leg is inverted, without asserting c is invertible.
   Mathlib `DerivedCategory.Q` is localization at the quasi-isomorphisms.
5. K-flat A-model P and R-model E, with P -> M and E -> P quasi-isomorphisms:
   the final universal clause quantifies `M P E p e`, `QuasiIso p`,
   `QuasiIso e` and both ordinary-module `quasiIso.kFlat` predicates.
   The two augmentation equations fix `es,et`; the equation
   `es.hom ≫ c.app M = Q.map ((extend R B).map e) ≫ et.hom`
   renders exactly the specified representative E tensor_R B -> P tensor_A A'.
6. Every cohomological degree: `∀ i : ℤ` relates H^i(c) to `comparison R A B i`
   through Mathlib `homologyFunctorFactors`. The localization theorem takes
   arbitrary `i : ℤ`, so it covers the same degrees.
7. A'-module structures on both cohomologies: functors `S,T` land in
   `ModuleCat (A ⊗[R] B)`. The B-linear natural isomorphisms `eS,eT` identify
   restrictions along includeRight with `source,target`. Their scalar equations
   identify includeLeft(a) with the image of `a • 𝟙 M`, the endomorphism
   specified by the node. This fixes the target's evident action too.
   Tensor-algebra modules incorporate commutation and agreement on R.
8. A'-linearity of H^i(c): `c : S ⟶ T` has linear components; its
   restriction equation with `eS,eT` identifies it with the canonical
   `comparison`, already tied to derived cohomology in the first theorem.
9. Every compatible prime: `q' : PrimeSpectrum (A ⊗[R] B)` and the three
   comapped ideals give q, p', p. `Rp,Aq,Bp,D` with four `IsLocalization.AtPrime`
   instances are arbitrary models of R_p, A_q, B_p', A'_q'. The scalar towers
   and `_hB` fix their canonical induced maps. Standard localizations supply
   every binder; these are presentation data, not extra flatness assumptions.
10. Local tensor ring and canonical map: `Aq ⊗[Rp] Bp` and `f`; `_hfA,_hfB`
    fix f on both tensor inclusions and therefore on all pure tensors.
    `Sl,Tl,eSl,eTl,cl` repeat the action and comparison characterization
    over Rp,Aq,Bp, without substituting a different local notion.
11. First natural localization identity: `alpha` identifies
    `S ⋙ extendScalars (algebraMap A' D)` with
    `extend A Aq ⋙ Sl ⋙ extendScalars f`; this is exactly the first
    displayed cohomology identity, D-linearly and naturally in M.
12. Second natural localization identity: `beta` first identifies the analogous
    localized target with `extend A Aq ⋙ Tl ⋙ extendScalars f`.
    The final `Nonempty` contains a natural isomorphism of functors from
    `Tl ⋙ extendScalars f` to
    `resolution Aq ⋙ extend Aq D ⋙ homologyFunctor D (.up ℤ) i`.
    Their composition is precisely H^i(M_q tensor-derived_Aq D).
13. Compatibility of comparison maps: the equation with `alpha.hom,beta.hom`
    is the commuting square between scalar extension of c and scalar extension
    of cl, precomposed with `extend A Aq`. Composing its target identification
    with the final natural isomorphism gives the node's localized comparison.
    Left tensor factors in `extendScalars` use the canonical commutative-ring
    tensor symmetry to render the node's right tensor convention.

Dependency check: I opened the three corrected statement dependencies and their
recorded signatures, including Mathlib Basic/HomologySequence for the abstract
category and `MorphismProperty.kFlat` in the source's Monoidal/KFlat module.
That predicate preserves quasi-isomorphisms under tensoring on both sides;
Abelian/Flat/KFlat's `CochainComplex.kFlat_iff_preservesQuasiIso` exposes exactly
the required specialization. I read all of RingTensorCohomology, including its
actual resolution choice, augmentation, span legs and comparison definition.
There are no private copies or new definition nodes/dependency modules in this
delivery. Its dependency's named `spanLeft_isIso` proof supports the comparison
definition; no data definition is hollow.

Citation correction check: the original `schemeDerivedCategory` takes a Scheme
and sheaf modules, and original `CochainComplex.IsKFlat` takes sheaves on a
ringed site (both source modules opened). They cannot type these ordinary-module
complexes. The recorded substitution to the abstract category and module K-flat
nodes, and citation of the existing ring tensor models, follows Stacks exactly.
I independently enumerated both dependency arrays of every DAG node: there is
only one direct citer, `lem-pc-rf-single-complex-affine-base-change`, so there is
no second citer to open. I read that citer's statement and all four proof steps:
its construction, A'-linearity, localization square and final isomorphism test
still use exactly these conclusions. Its `holds: true` verdict is correct.
No blueprint unit statement or mathematical clause is changed by the correction.

Edge cases: zero rings and zero complexes are allowed; for a zero tensor ring
there are no q', while the comparison and action assertions persist. Complexes
are unbounded; i can be zero, negative or positive. No scheme, index set, n or
characteristic is constrained. The familiar R=k[t], A=B=k example can have
noninvertible comparison and is admitted. The common arbitrary universe u can
be the maximum of the ring and module universes by cumulativity; it is not a
small fixed universe. The independently bound w merely chooses the derived
localization's morphism universe; Mathlib supplies the standard larger choice.
All localization models may be taken in u and none of these quantifiers is
vacuous for a prime. There are no unbound variables (`autoImplicit false`).

Independent searches, using wording different from the worker:

- LeanFinder: `localization of derived scalar extension comparison for complexes
  of modules` returned eight hits, including exact-functor maps on Ext,
  localized-module scalar extension and linearity of localization functors;
  none states this comparison with its prime-localization square.
- Loogle: `DerivedCategory.Q, NatTrans` was rejected for unknown NatTrans,
  so I reran `DerivedCategory.Q`; twelve hits give Q and its standard
  localization/shift/additive facts, not this statement.
- LeanSearch: `cohomology of derived tensor product localized at a prime
  comparison morphism` returned Internal Server Error. This is unavailable,
  not evidence of absence.
- Direct rg over project Sheaf, source WeilConjectures, Mathlib homological
  algebra and localization: `base.?[Cc]hange.*[Cc]omparison`,
  `comparison.*[Ll]ocal`, `derived.*[Ll]ocaliz`, `[Ll]ocaliz.*derived`.
  I opened the candidate DerivedTensorFlatSecondLocalization module: it is
  second-factor flat localization, not both prime-localization identities.
  I also opened BaseDerivedTensorCohomologyModel: it defines a universal model
  and its counit/localization map, not this theorem. RingTensorCohomology is
  reused rather than duplicated. The exact two delivered theorem names have
  no hits in Mathlib, WeilConjectures, project Sheaf or lean_names_upstream.json.

No mathematical mismatch was found. I left the correct Lean and node unchanged
and added this independent reading and search record. Both theorem proofs are
`by sorry`; there are no new definitions or proved results. Module and theorem
docstrings name the source and blueprint item and carry the DAG's construction,
scalar-action, localization and compatibility proof steps. All lines meet the
100-character convention. The stored primary `lean.statement` matches the
first theorem's signature; `lean.declarations` names both component theorems.
Independent server compilation via scompile.py completed cleanly, exit 0,
in 3.0 seconds, with no errors or warnings.
