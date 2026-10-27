## Worker report

Item: lem-trf-half-bounded-hom-scalar-isomorphism. The delivered module is
`Sheaf.Algebra.Homology.HalfBoundedHomScalarIsomorphism`. It states the actual
complex isomorphism, its degree-dependent stupid-tail comparison, and naturality.
Only the item's `lean` record changes; there are no new nodes, dependency repairs,
or statement corrections. The two theorem proofs are `sorry`; no proof is attempted.

The source read is `literature/stacks-project/more-algebra.tex`,
`lemma-internal-hom-evaluate-tensor-isomorphism` (Tag 0ATK), especially the finite
sum computation in the proof of (3), lines 28653 onward. This delivery states the
node's chain-level degree-zero-scalar specialization, rather than adding the
K-flat representative conditions used for the derived assertion in that source.

Clause-by-clause correspondence:

- Arbitrary commutative rings and ring map: `{R S : Type u} [CommRing R]
  [CommRing S] (φ : R →+* S)`. A common universe is arbitrary; the singleton-site
  API uses that same universe for sections and coefficients.
- Ordinary integer cochain complexes identified with punctual module sheaves:
  `P N : CochainComplex (RingSiteModules R) ℤ`. This is exactly the one-object,
  identity-only, bottom-topology model permitted by the node. The imported
  singleton-site comparison identifies it with ordinary modules; it is not a
  restriction to general sheaf complexes with some different geometry.
- The termwise scalar extension F is specified by `(F : RingSiteModules R ⥤
  RingSiteModules S)`, object equalities `h`, the transported scalar-extension
  map equalities `hm`, and `hF : F.Additive`. These data specify the functor in
  the node, rather than adding a preservation or flatness assumption. The given
  objects are exactly `SheafOfModules.changeOfRings (ringSiteMap φ) M` and its
  specified map. On complexes it is the existing `ringExtensionComplex F hF`.
- Integers a,b, upper bound on P, finite freeness of every term, lower bound on N:
  `(a b : ℤ)`, `hP : ∀ p, b < p → IsZero (P.X p)`, `hfree : ∀ p,
  Module.Free R ((P.X p).val.obj (op ⟨PUnit.unit⟩))`, `hfinite` with
  `Module.Finite R` on the identical module, and `hN : ∀ q, q < a →
  IsZero (N.X q)`. Free plus finitely generated is finite free, including the
  zero module over the zero ring. Only evaluation at the unique object is used.
- The Hom complexes are the existing `homComplex`, not a new Hom construction.
  Their chosen projections, degree terms, differential sign and functoriality
  are those of def-pur-hom-complex; evaluation gives the ordinary module-valued
  `CochainComplex.moduleHomComplex` of def-sc-module-total-hom-complex.
- The normalized chain map and its formula are fixed by the definition
  `halfBoundedHomScalarMap := (normalizedRingHomExtension_exists φ F h hm hF
  P N).choose`. The chosen theorem's predicate is exactly
  `ringHomEvaluate FP FN n p U (χ(b ⊗ f)) (c ⊗ x) = bc ⊗ f_p(x)`, with the
  shared projection and `ringExtensionPure` sheafification/unit conventions.
  Pure tensors generate on this bottom site; evaluation and all product
  coordinates detect equality. Hence this specification determines a unique
  map, not arbitrary data chosen from a bare existence theorem. The upstream
  existence theorem is proved, and its actual normalized construction is reused.
- Isomorphism of complexes: the main conclusion is `∃ e : F•(Hom(P,N)) ≅
  Hom(F•P,F•N), e.hom = halfBoundedHomScalarMap ...`. Its inverse is a chain
  map by its type; thus the inverse degree maps commute with the differentials.
  The conjunct `∀ n, IsIso ((halfBoundedHomScalarMap ...).f n)` states the
  requested degreewise invertibility explicitly as well.
- For each n, c=a-n and P_c: the theorem uses the literal expression
  `P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - n))`. There is no good
  truncation, derived localization, or replacement by a quasi-isomorphic tail.
- Restriction isomorphisms: `rR` and `rS` have exactly the two degree-n Hom
  objects in the node as source and target. Their `hom` fields equal the
  degree-n maps of `homComplexFunctor.map` applied to `P.ιStupidTrunc ...`,
  respectively its termwise scalar extension. These are actual restriction of
  homogeneous families; no arbitrary isomorphism can satisfy an alternative
  normalization. In retained degrees the inclusion is the identity under
  `stupidTruncXIso`, so the inverse identities force every retained component
  to be unchanged. The last two conjuncts explicitly state that `rR.inv` and
  `rS.inv` evaluate to zero for every p<c: the omitted components are inserted
  as zero, over both rings.
- Agreement with the bounded finite-free comparison: the equation
  `χ.f n ≫ rS.hom = F.map rR.hom ≫ (χ for P_c,N).f n` is precisely the
  conjugation square. Since rR and rS are isomorphisms, it is equivalent to
  `rS χ^n F(rR⁻¹)` being the normalized comparison for P_c. That comparison
  uses the same existing normalized-map constructor for every tail.
- Naturality in cochain maps: `halfBoundedHomScalarMap_naturality` takes
  `α : P' ⟶ P` and `β : N ⟶ N'`. It states the square using the existing
  contravariant and covariant actions of `homComplexFunctor` and termwise F.
  This formula holds even before imposing bounds, and therefore on all the
  bounded objects of the main theorem. Composing the square with the inverse
  chain maps of the isomorphisms yields inverse naturality as in DAG step 6.
- No flatness, Noetherian, perfectness, or K-flatness binder occurs. There is no
  assertion that a stupid tail represents the derived object of P.

Dependency declarations read and reused:

- lem-weil-pbc-singleton-site-module-comparison:
  `Sheaf.ProperBaseChange.SingletonSiteModuleComparison`,
  `CategoryTheory.singleton_site_module_comparison`; its full signature and
  ten-step docstring identify the actual punctual-site tensor/unit model.
- def-sc-module-total-hom-complex:
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`,
  `CochainComplex.moduleHomComplex`, whose terms are Mathlib homogeneous
  cochains and whose differential is `HomComplex.δ_hom`.
- def-pur-hom-complex: `WeilConjectures.Algebra.Homology.HomComplex`,
  `CategoryTheory.homComplex`, `homComplexFunctor`, and `homComplex_exists`.
- lem-pc-normalized-ring-hom-extension:
  `Sheaf.Algebra.Homology.NormalizedRingHomExtension`,
  `CategoryTheory.normalizedRingHomExtension_exists`. Its public dependency
  `RingHomExtensionDefs` provides `RingSiteModules`, `ringSiteMap`,
  `ringExtensionComplex`, `ringExtensionPure`, and `ringHomEvaluate`.
- def-kun-truncations:
  `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits` publicly imports
  Mathlib's `HomologicalComplex.stupidTrunc` and the integer embeddings, as its
  module documentation specifies for the truncation part of that composite
  node. Its main declaration `CategoryTheory.IsSequentialHomotopyColimit` is
  not mistaken for a truncation. The actual inclusion is the existing
  `HomologicalComplex.ιStupidTrunc` from
  `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc`.
- Proof dependencies: `Module.Finite` in `Mathlib.RingTheory.Finiteness.Defs`,
  `Module.Projective` in `Mathlib.Algebra.Module.Projective`,
  `CategoryTheory.finiteProjectiveRingHom_extension_exists` in
  `Sheaf.Algebra.Homology.FiniteProjectiveRingHomExtension`, and
  `CategoryTheory.boundedRingHom_extension_degree_isIso` in
  `Sheaf.Algebra.Homology.BoundedRingHomExtensionDegree`. Their full signatures
  and docstrings were read. Proof-only imports are plain imports; finiteness is
  also used to express finite freeness in the signature and is imported publicly.

Edge cases checked mathematically before writing: zero P or zero N; R or S the
zero ring; a nonflat scalar map such as ℤ→ℤ/2; negative a,b,n; c>b (empty interval,
all degree-n factors zero); c=b (one possibly nonzero factor); and an unbounded
lower tail of P with unbounded upper tail of N. Only p in [a-n,b] can contribute
in degree n, so there are finitely many factors in every case. These checks also
show why no flatness is used and why the tail is not asserted to be a derived
replacement. The zero-ring case admits the empty basis and is not excluded.

Searches actually run with msearch.py for this group/item:

- leanfinder: `Scalar extension commutes with total Hom for bounded above finite
  free and bounded below cochain complexes`. Eight hits, chiefly
  `HomologicalComplex.extendMap` and Ext scalar-composition lemmas; none is this
  chain-level comparison or its truncation refinement.
- loogle: `ModuleCat.extendScalars, CochainComplex.HomComplex`. Zero hits.
- grep (Mathlib/Algebra/Homology):
  `halfBounded|half_bounded|normalizedRingHomExtension|moduleHomComplex`.
  Zero hits.
- leansearch: `Scalar extension of the Hom complex of a bounded above complex
  of finite free modules and a bounded below complex is an isomorphism`.
  Eight hits, including the ordinary module extension/restriction adjunction
  and `HomologicalComplex.extendXIso`; none states the product-Hom comparison.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: the item id, halfBoundedHom names, and
  normalizedRingHomExtension. No existing item statement or proposed name.
  The existing normalized chain map and its use in PerfectRHomBaseChangeMap
  were found and reused. Searches for stupid truncations located the Mathlib
  construction and the existing upstream inclusion, avoiding new definitions.
- Direct rg in Mathlib's HomComplex source for scalar/base-change/extension
  comparisons found no matching declaration. The exact signatures/docstrings
  of all dependency declarations above were opened directly.

Validation: initial scompile.py run passed in both sandbox and final module
names (2.8 s and 3.0 s), without errors or warnings. The final file, including the public-import adjustment, also passed
`deliver2.py Q49 lem-trf-half-bounded-hom-scalar-isomorphism --no-push`: the
wrapper reported OK, with preflight and both module-name compiles passing.

## Second reading by Q49

This is an in-thread second pass; the dispatcher explicitly prohibits starting
another agent. The maintainer supplies the independent review after delivery.
I reread the node and final module together. The bound directions are b<p for P
and q<a for N, both strict; the cutoff is a-n, with the equality degree retained.
The two restriction targets use F(P_c), not a newly truncated F(P) with an
unprovided comparison. Both maps are fixed by the existing inclusion, and the
scalar square has source F(Hom(P,N)^n) on both paths. The inverse zero conditions
quantify over original P or F(P), exactly the components lost by restriction.
The complex iso pins its forward map to the existing normalized construction,
and its inverse already includes the differential equations. Naturality has
P contravariant and N covariant, with α:P'→P and β:N→N'. I also checked the
literal pure-tensor formula in the selected dependency theorem, including the
shared projections and tensor order. The only adjustment was making the
finiteness-definitions import public because `Module.Finite` occurs in the
signature. No mathematical statement mismatch or node correction was found.
