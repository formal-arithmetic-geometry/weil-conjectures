## Worker report

The module `Sheaf.RingTheory.ProEtale.ClosedLiftMap` completes the existing upstream
closed-lift construction with `Algebra.ClosedLift.postcomp` and `Algebra.ClosedLift.map`.
No existing construction is copied. All three newly stated theorems have `sorry` proofs;
the definitions contain actual data. No node statement is changed and no new node is needed.

Hypotheses and clauses:

- The commutative base ring and input algebra are `A C : Type u`, `[CommRing A]`,
  `[CommRing C]`, `[Algebra A C]`. For the node's input take an ideal `I : Ideal A`,
  `[Algebra (A ⧸ I) C]`, `[IsScalarTower A (A ⧸ I) C]`, and
  `[Algebra.IndEtale (A ⧸ I) C]`. The construction, just as its existing upstream
  declaration, does not use the quotient or ind-etaleness; it is defined on every
  A-algebra and restricts to precisely these inputs. No extra assumption is required.
- Objects `(B,q)` and all compatible morphisms are the existing
  `Algebra.ClosedLift.Index A C` and `Index.Hom`: `n`, `rel`, `etale`, `toC`,
  and fields `hom`, `comp_toC`. The category instance uses algebra-map identities and
  composition. The quotient polynomial rings lie in `Type u`, and the indexing category
  is small in the same universe. The node's finite-list presentation model and this
  upstream ideal model are equivalent: each etale quotient is finitely presented,
  so its relation ideal is finitely generated; forgetting a finite generating list is
  essentially surjective and fully faithful since morphisms ignore presentations.
  Thus the chosen colimit construction uses the already established presentation model,
  without creating a second definition of the notion. Repeated and empty lists are
  allowed in the finite-list description and do not change this equivalence.
- The etale condition is upstream `Index.etale : Algebra.Etale A B`.
  This is the affine form of the recorded `AlgebraicGeometry.Etale` condition.
  `Algebra.Etale.finitePresentation` supplies the finite-presentation requirement.
- The diagram on objects and morphisms is the existing `Algebra.ClosedLift.diagram`:
  `CommAlgCat.of A X.alg` and `CommAlgCat.ofHom f.hom`.
- The chosen colimit algebra is the existing `Algebra.ClosedLift A C`, definitionally
  the carrier of `colimit (diagram A C) : CommAlgCat A`. Its structure maps are
  `(colimit.ι (diagram A C) X).hom`.
- The retained epsilon is the existing `Algebra.ClosedLift.toAlgHom A C`, obtained
  by `colimit.desc` from the existing `coconeC`, whose components are `X.toC`.
  `ι_toAlgHom` states exactly epsilon composed with the structure map equals q.
- For another input `C'`, the variables carry `[CommRing C'] [Algebra A C']`.
  An A/I-algebra map is used through its restriction to an A-algebra map
  `φ : C →ₐ[A] C'`. Its extra scalar compatibility is not needed by this construction.
- `postcomp φ` sends X to `⟨X.n, X.rel, X.etale, φ.comp X.toC⟩` and sends a
  compatible algebra map to the same `f.hom`. The named theorem
  `postcomp_compatible` supplies only the equality proof needed for that morphism.
- `map φ` is the algebra map underlying `colimit.desc` of the target colimit cocone
  whiskered by `postcomp φ`. Its components are precisely the structure maps
  indexed by `(B,φ ∘ q)`. The theorem `ι_map` is the final displayed identity,
  in Lean's algebra-map composition order.

Dependency declarations read and used:

- `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes the recorded
  `Algebra.IndEtale` from `WeilConjectures.RingTheory.ProEtale.IndEtale`.
  Its definition is existence of a small filtered `ColimitPresentation` with etale terms.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.ι`,
  `colimit.desc`, `colimit.cocone`, `colimit.isColimit`; available through the
  upstream construction's public import closure.
- `Mathlib.Algebra.Category.CommAlgCat.Basic`: the recorded anonymous
  `HasColimits (CommAlgCat A)` instance (the dependency's mathlib_match
  names its generated name `instHasColimitsCommAlgCat`).
- Existing construction reused from
  `WeilConjectures.RingTheory.ProEtale.ClosedLift`, whose full source was read:
  `Index`, `Index.Hom`, its category instance, `diagram`, `coconeC`,
  `Algebra.ClosedLift`, and `toAlgHom`.

Edge cases checked: zero base and zero input rings are allowed (no `Nontrivial`);
`I = ⊥` and `I = ⊤` impose no special restriction on these constructions;
`n = 0` and empty relation lists are allowed. The indexing category contains the
identity A-algebra presentation for every input, including the zero input.
Morphisms include every compatible algebra homomorphism, without injectivity or
surjectivity restrictions. No filteredness hypothesis is used to form the colimit.
All universe and type variables are explicit, with the index and algebras in the
same universe, as required by the recorded colimit instance.

Searches performed:

- `msearch.py leanfinder`: "Colimit of finitely presented etale A algebras mapping
  to C functorial by postcomposition". Eight results, including
  `Algebra.Etale.finitePresentation`, `Algebra.Etale.exists_subalgebra_fg`,
  finite-presentation factorization lemmas, and standard etale presentations;
  no full construction or induced-map definition.
- `msearch.py loogle`: "Algebra.ClosedLift, CategoryTheory.Limits.colimit.pre".
  No hits, unknown identifier `Algebra.ClosedLift` in the search index.
- `msearch.py grep`: "ClosedLift|closedLift|closed_lift". No Mathlib hits.
- `msearch.py leansearch`: "Functorial colimit of etale algebras mapping into an
  algebra". Service unavailable: Internal Server Error; no verdict inferred.
- `rg` of upstream `WeilConjectures` and project `lean/Sheaf` for
  `ClosedLift|closedLift|closed_lift|indEtale.*Lift|EtaleNeighbourhood|etaleNeighbourhood`:
  upstream `RingTheory/ProEtale/ClosedLift.lean` has the object construction,
  and `AlgebraicGeometry/ProEtale/ClosedCoverExtension.lean` uses it; no induced map.
- `rg` of upstream, project, and `dag/lean_names_upstream.json` for
  `ClosedLift.*(map|postcomp)|closedLiftMap`: no declaration of the needed maps.
- `grep -rn def-exc-ind-etale-closed-lift` in upstream: only the existing partial
  construction's source docstrings. This confirmed the partial reuse described above.

Source checked: the entire blueprint node
`sec-smooth-purity/sk-prop-sf-open-closed-triangle/def-exc-ind-etale-closed-lift.md`.
No statement dispute or dependency fault was found.

Validation: server-only `scompile.py`, nice 19, two threads, 60 seconds per file;
initial and final compiles clean, with no warnings. The first dry run found only
the signature parser excluding the `noncomputable` modifier and the missing
second-reading section. The record now follows the tool's verbatim signature
convention; the section below explicitly awaits the independent reader.

## Earlier second reading (a previous round; superseded)

Pending independent second reader. This is the worker dry run only; no second
reading has occurred and this delivery has not been pushed. The dispatcher's
fresh second reader must replace this paragraph with their actual review.

## Second reading by NE

Independent second reader, 2026-10-15. I opened the delivered node and module,
the complete blueprint source at
`sec-smooth-purity/sk-prop-sf-open-closed-triangle/def-exc-ind-etale-closed-lift.md`,
all five statement-dependency records and their declarations. I read the exact
upstream `lean/WeilConjectures/RingTheory/ProEtale/ClosedLift.lean` in the group
clone, and `coord/pefw-upstream-framework.md`; I did not substitute declarations
from the older source tree for that construction. The primary source is this
blueprint definition, not a Stacks lemma. I also checked the underlying Stacks
finite-presentation, etale-morphism and colimit definitions. There is no implicit
Noetherian, nonzero, field, characteristic, or finite-ideal hypothesis.

The node's objects, hypotheses and clauses, matched individually:

1. A commutative base ring A: `{A : Type u} [CommRing A]`. The input C is
   `{C : Type u} [CommRing C] [Algebra A C]`. For the source's domain one supplies
   `I : Ideal A`, `[Algebra (A ⧸ I) C]`, `[IsScalarTower A (A ⧸ I) C]` and
   `[Algebra.IndEtale (A ⧸ I) C]`. The recorded dependency exposes precisely this
   last predicate: a small filtered `ColimitPresentation` with etale terms.
   Verdict: the existing construction and new definitions accept these inputs
   without any additional hypothesis. I and ind-etaleness are not needed to
   define the object or maps; no theorem about lifting or reduction has been
   asserted for more general inputs here.
2. Objects are etale finitely presented A-algebras B with A-algebra maps q to C.
   `Index A C` has `n`, `rel`, `etale`, `toC`, and its algebra is
   `MvPolynomial (Fin n) A ⧸ rel`. `Index.etale` is `Algebra.Etale`, whose
   `finitePresentation` field gives the recorded `Algebra.FinitePresentation`.
   `AlgebraicGeometry.Etale` is affine-locally `RingHom.Etale`, and
   `RingHom.etale_algebraMap` identifies that affine condition with
   `Algebra.Etale`. Verdict: the same etale and finite-presentation conditions.
3. Size is handled by finite polynomial presentations. The node describes
   finite relation lists; upstream records their generated ideal. This does
   not introduce non-finitely-presented objects: specifically
   `Algebra.FinitePresentation.ker_fg_of_mvPolynomial` applied to the canonical
   surjection onto the quotient shows that every such `rel` is finitely
   generated. A finite generating set can be listed. Forgetting that list is
   fully faithful (the hom types depend only on the algebras and q) and
   essentially surjective; it preserves the underlying algebra diagram.
   Verdict: equivalent small presentation models with corresponding chosen
   colimits. Reusing this existing model is appropriate, rather than creating
   a second closed-lift definition.
4. Morphisms include every A-algebra f with q' composed with f equal to q:
   `Index.Hom.hom` and `comp_toC`. Its category instance uses `AlgHom.id` and
   `g.hom.comp f.hom`. Verdict: all compatible maps, with the correct direction,
   identities and composition; no restriction depending on presentations.
5. The diagram sends `(B,q)` to B and f to f: existing `diagram`, with
   `CommAlgCat.of A X.alg` and `CommAlgCat.ofHom f.hom`. Verdict: exact.
6. H is the chosen colimit in commutative A-algebras: existing
   `Algebra.ClosedLift A C` is the carrier of `colimit (diagram A C)`.
   The ring and A-algebra instances come from that object. The dependency's
   `HasColimits (CommAlgCat.{u} A)` instance supplies existence. Its structure
   maps are `(colimit.ι (diagram A C) X).hom`. Verdict: exact, with the recorded
   categorical colimit, rather than an unrelated ring construction.
7. Epsilon is induced by q: existing `coconeC` has components X.toC, and
   `toAlgHom` is its `colimit.desc`. New `ι_toAlgHom` states precisely
   `(toAlgHom A C).comp (colimit.ι (diagram A C) X).hom = X.toC`.
   Verdict: both the retained map and every required factorization identity.
8. Another ind-etale A/I-algebra C' and an A/I-algebra map phi: C' has the same
   ring and A-algebra binders as C. Restricting phi's scalars to A supplies
   `φ : C →ₐ[A] C'`. Its A-linearity follows from the quotient scalar towers.
   Verdict: every source map is accepted; the definitions need no additional
   constraint or choice of an A/I-linear lift.
9. Postcomposition sends `(B,q)` to `(B,phi composed with q)` and f to f:
   `postcomp.obj X := ⟨X.n, X.rel, X.etale, φ.comp X.toC⟩`, and its map is
   `⟨f.hom, postcomp_compatible φ f⟩`. The named compatibility theorem states
   exactly the associativity/substitution equality needed. Verdict: exact.
10. H(phi) is induced by components iota at `(B,phi composed with q)`:
    `map` is `colimit.desc` of the target colimit cocone whiskered by
    `postcomp φ`, followed by `.hom`. This whiskered diagram is definitionally
    the original diagram because postcomposition leaves B and f unchanged.
    `ι_map` states the node's last displayed identity, for every X, in
    AlgHom composition order. Verdict: exact, with the same quantifier order.

Edge cases: n = 0 is permitted by `n : ℕ`, and the zero relation ideal permits
an empty relation list. Redundant lists are forgotten without changing maps.
There is no `Nontrivial` assumption: zero rings, the empty affine scheme,
I = bottom or top, and every characteristic are included. The construction
requires no filteredness instance to form its colimit. The index is actually
nonempty (the zero-variable presentation of A maps to every input); it is not
restricted by a hidden nonempty-index assumption. All rings, polynomial
quotients, objects and hom types use the same arbitrary universe u, matching
the recorded colimit and ind-etale conventions. No independent smaller test
universe, unbound universe, or implicit variable remains.

Independent searches, with alternative wording:

- LeanFinder: "Functor on etale algebra factorizations induced by a homomorphism
  on the target algebra"; eight hits including `StandardEtalePair.HasMap.map`,
  `StandardEtalePair.homEquiv`, and `Algebra.Etale.comp`. None defines this
  postcomposition functor or its induced closed-lift map.
- Loogle: `CategoryTheory.Limits.colimit.pre`; twelve hits. This is the general
  colimit reindexing API, not an existing closed-lift construction. The module
  already uses the equivalent general descent API, without redefining it.
- LeanSearch: "Induced morphism of colimits of etale algebra factorizations by
  postcomposition"; unavailable (HTTP 521), with no negative verdict inferred.
- `rg` over Mathlib, the full upstream `WeilConjectures`, the group clone's
  `lean/WeilConjectures`, and `lean/Sheaf`, using
  `ClosedLift.(map|postcomp|ι_toAlgHom|ι_map)`, `closedLiftMap`,
  `etaleApproximation`, and `etaleHull`: no existing declarations of these
  additions. Broader `EtaleNeighbourhood`/`etaleApprox`/`postcomp` searches and
  opening `ClosedLift.lean` confirm that the existing object, diagram and
  epsilon are reused, and only functoriality is missing there.

No new nodes or dependency modules are present, and no statement correction
is needed. Both new definitions contain concrete data. Their only postponed
compatibility proof is a named theorem with its own source and proof docstring;
all three new theorems have `sorry` as their whole proof. The node has no proof
steps to import. Module and declaration docstrings carry the source and
blueprint id. Imports expose the recorded dependency notions; names, public
visibility, line lengths and the verbatim `lean.statement` were checked.

Mismatches found: none requiring a code or node change. I left the Lean and
node record unchanged and added this independent clause-by-clause review.
Server validation through `scompile.py` passed: `ClosedLiftMap.lean` in 1.7 s,
with its side dependency `IndPrincipalZariski.lean` in 1.3 s; nice 19, two
threads, a 60-second per-file limit, and no warnings or errors.
