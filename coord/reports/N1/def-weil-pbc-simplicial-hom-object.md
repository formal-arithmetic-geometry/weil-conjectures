## Worker report

The module `Sheaf.AlgebraicGeometry.SimplicialHomObject` defines the compatible
simplicial family notion, its contravariant functor by precomposition, a representing
pair and the selected object `simplicialHomObject`, together with the universal bijection
and restriction morphism. The binders `X`, `K`, `S`, finiteness and nonemptiness hypotheses
are exactly those in the node. Compatibility is the equation
`f n s ≫ K.map φ.op = f m (S.map φ.op s)` for every simplex operator; precomposition
renders functoriality. The representing pair uses `CategoryTheory.Functor.IsRepresentedBy`.
The existence theorem is a named `sorry` statement, so no definition contains sorry data.

Dependencies used: `Sheaf.AlgebraicGeometry.SemiRepresentableObject` (the
`FormalCoproduct X.Etale` category), `Sheaf.AlgebraicGeometry.SimplicialHomObjectExists`
(`exists_simplicial_hom_object`), `Mathlib.CategoryTheory.RepresentedBy`
(`Functor.IsRepresentedBy`), and Mathlib simplicial set declarations (`SSet`,
`SSet.Subcomplex`). The empty and singleton index cases are allowed; no lower bound on
simplex degrees is imposed, and arbitrary universes `u`, `w`, and `t` are retained.
Searches: `msearch.py leanfinder` for a presheaf of compatible simplicial families
returned unrelated Cech and standard-simplex declarations; `loogle` for
`CategoryTheory.Functor.IsRepresentedBy, CategoryTheory.SimplicialObject` returned no
hits; grep for `cotensor|homFromSSet|simplicialHomObject` in Mathlib returned no hits;
LeanSearch was unavailable. Grep of the project found no existing declaration.
The Stacks source consulted is Definition 017I and Lemma 017K (Tags 017I, 017K).

## Earlier second reading (a previous round; superseded)

Read the node and module independently. Each node clause is rendered: the semi-representable
category is `FormalCoproduct X.Etale`; an S-family is the subtype of all maps with every
simplicial compatibility equation; precomposition is the specified contravariant action;
representability is `IsRepresentedBy`; the chosen object comes from the existence theorem;
and a simplicial subset restriction is defined on restricted simplices. No hypotheses or
edge cases were added or removed. The existence proof is explicitly named and remains
`sorry`, as required for stage 2.

## Second reading by N1

I read the item, all five statement dependency nodes and their recorded declarations,
the delivered module, and Stacks simplicial.tex section 017H, definition 017I and
lemmas 017J/017K, together with categories.tex definition 001Q and the following
universal-object paragraph. The local repository has no Stacks checkout; I read the
available source copies in `/home/ubuntu/c1-stacks-review/`. The source assumes binary
coproducts and finite limits in 017K, supplied here by the category of formal families
of étale schemes. It assumes degreewise finite, nonempty simplices and eventual
degeneracy. With degreewise finiteness, eventual degeneracy is equivalent to finitely
many nondegenerate simplices, exactly `SSet.Finite`. No base field, characteristic,
Noetherian, quasi-compactness or separation hypothesis is involved.

Object/hypothesis/clause checklist (the list was taken from the node before review):

1. A scheme X and its small étale site: `{X : Scheme.{u}}` and `X.Etale`.
   I opened `Scheme.Etale` and `smallEtaleTopology` in Mathlib: these are étale
   X-schemes, X-morphisms, and the jointly-surjective topology recorded by
   def-weil-pbc-etale-site. Verdict: same site; this object construction does not
   require a topology binder.
2. SR(X), arbitrary W and W', and simplicial K with contravariant operators:
   `FormalCoproduct.{w} X.Etale`, `SimplicialObject` and `K.map φ.op`.
   I opened SemiRepresentableObject.lean and FormalCoproducts/Basic.lean:
   the index set and component maps are exactly the dependency node's formal
   families, with its finite-limit instance and singleton inclusion. Verdict: exact.
3. S, its finite nonempty degree sets, and finitely many nondegenerate simplices:
   `S : SSet.{t}`, `hfinite : ∀ n : ℕ, Finite (S.obj (op ⦋n⦌))`,
   `hnonempty : ∀ n : ℕ, Nonempty (S.obj (op ⦋n⦌))`, and `[S.Finite]`.
   I opened Basic.lean, Subcomplex.lean and Finite.lean: SSet is a contravariant
   functor on Delta; Finite means finiteness of the set of all nondegenerate
   simplices. Verdict: all three hypotheses present, none stronger.
4. One map W → K_n for every degree and simplex, with every operator equation:
   `SimplicialHomFamily` is the subtype of `∀ n, S.obj (op ⦋n⦌) →
   (W ⟶ K.obj (op ⦋n⦌))` with `f n s ≫ K.map φ.op = f m (S.map φ.op s)`.
   The binders m, n, φ and s have exactly the node's order and ranges.
   Verdict: exact, including degeneracies and degree zero.
5. Precomposition and the contravariant functor: `SimplicialHomFamily.precomp`
   has components `g ≫ f.val n s`; `simplicialHomFamilyFunctor` maps an opposite
   arrow g by precomposing with `g.unop`. Its identity/composition fields are
   definitional `rfl` equalities of maps, using proof irrelevance for subtype
   certificates. Verdict: correct variance and functor laws.
6. Any representing pair with universal family: `SimplicialHomRepresentation`
   has `obj`, `universal`, and `represents : ...IsRepresentedBy universal`.
   I opened Mathlib RepresentedBy.lean: its field is bijectivity of the actual
   precomposition map for every W, with no same-universe restriction. Verdict:
   exactly the node's pair, rather than an arbitrary unexplained equivalence.
7. Existence and a fixed choice: `exists_simplicialHomRepresentation` takes
   precisely the three S hypotheses; `simplicialHomRepresentation` chooses that
   pair; `simplicialHomObject` projects its object. I opened the dependency
   `exists_simplicial_hom_object`: it supplies H, the compatible universal maps
   and unique factorization under exactly these binders. The docstring now
   explains bundling these into IsRepresentedBy. Verdict: no hollow data.
8. The universal bijection, including T-points: `R.homEquiv W` uses
   `R.represents.representableBy.homEquiv`. Mathlib's
   `IsRepresentedBy.representableBy_homEquiv_apply` is rfl and identifies its
   value with `F.map g.op R.universal`, hence components `g ≫ u n s`.
   Specializing W to `(FormalCoproduct.incl X.Etale).obj T` gives the dependency's
   `semiRepresentablePoints`, for every T of X.Etale. Verdict: both clauses exact.
9. A simplicial subset A and restriction of families: `A : S.Subcomplex` and
   `A.toSSet` use the dependency's Subfunctor, so operators are restrictions.
   `f.restrict A` uses `f.val n s.val` and the same compatibility certificate.
   Verdict: exactly the node's family restriction, also available without any
   finiteness hypothesis because restricting an existing family needs none.
10. Restriction between the fixed pairs, its defining equations, uniqueness,
    and compatibility with precomposition: `R.restriction A R'` is
    `(R'.homEquiv R.obj).symm (R.universal.restrict A)`. The inverse equivalence
    makes it the unique arrow whose universal family is the restricted one.
    Componentwise composition shows that restricting `R.homEquiv W g` gives
    `R'.homEquiv W (g ≫ R.restriction A R')`. Verdict: all clauses follow from
    the definition and the supplied IsRepresentedBy proof. The constructor
    accepts any given pairs, as the node says; the named choices instantiate it
    for admissible S and A. It adds no existence assertion for non-admissible A.

Edge cases: empty formal-family index sets and singleton families are allowed by
`FormalCoproduct.I : Type w`. The empty simplicial set, and an empty A, are excluded
by the node's explicit degreewise nonemptiness for choosing objects; the worker
report's phrase "empty ... index cases" must not be read as asserting otherwise.
The general family/restriction operations still make sense for empty S or A.
The empty scheme is allowed. No zero object is assumed in SR(X), which need not
have one. Degree n = 0 is explicitly included by ℕ. There is no characteristic
restriction. Universes u (schemes), w (family indices) and t (simplices) are all
bound and independent, and the presheaf takes values in `Type (max u w t)`;
no small-universe quantifier silently excludes test objects or families.

Independent searches (recorded by msearch.py):

- LeanSearch: "representing compatible maps from simplices into a simplicial
  object in a category"; the service returned Internal Server Error, recorded
  unavailable, with no mathematical verdict inferred from it.
- LeanFinder: "cotensor of a simplicial diagram by a finite simplicial set in a
  finitely complete category"; results were SSet monoidal structures and finite
  products, not this SR(X) representing pair.
- Loogle: `"SimplicialObject", "limit"`; results were pointwise (co)limit
  instances on simplicial/cosimplicial objects, not the stated construction.
- Grep of all Mathlib for `cotensor|weightedLimit|simplicialHom|homFromSimplicial`
  found weighted-limit infrastructure and unrelated homotopies/cotensorators.
  I opened Limits/Weighted/HasWeightedLimit.lean: weightedLimObjObj requires
  `[HasWeightedLimit W F]` and gives a chosen limit of the category-of-elements
  diagram. It does not state the admissibility-based existence or define the
  universal-family presheaf and arbitrary representing pair of this node.
  Its weighted cones are useful generic proof infrastructure, not an exact
  existing declaration for this item's statement.
- Independent rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `simplicialHom|SimplicialHom|cotensor|weightedLimit|homFromSimplicial`
  found only unrelated upstream pullback cotensorators. I also inspected
  SimplicialCategory.sHom: it is the enriched simplicial mapping set of an
  already simplicially enriched category, not an object of SR(X). No exact
  existing declaration found, so the module remains.

Mismatches repaired: the compatibility proof needed by the precomposition
constructor was embedded in its definition. It is now the named, sorry-only
`SimplicialHomFamily.precomp_compatible`, carrying the explicit associativity
and compatibility argument and listed in the node's lean.declarations. The
existence theorem's former one-line source citation lacked a takeover-ready
proof; it now gives the four steps reducing to the recorded existence dependency
and bundling its unique factorization into IsRepresentedBy. The node's TeX
statement, statement dependencies and main Lean signature required no change.
The new compatibility theorem is a proof obligation of this very definition,
not a new mathematical notion; it is carried by this node. No new nodes or
additional dependency modules are delivered. All declarations have source
and blueprint docstrings; no unbound variable, file-local notation, private
notion or sorry data remains. The two theorem proofs remain sorry, as stage 2
requires. Local compilation after the repair was clean (exit 0, no warnings).

## Stage-2 fix by R-sho (2026-10-12)

H5: `simplicialHomObject` was data taken by `Classical.choice` from the sorried
`exists_simplicialHomRepresentation`, itself a second spelling (H4) of the landed
`exists_simplicial_hom_object`. Dropped `SimplicialHomRepresentation` (a bundle of Mathlib's
`Functor.IsRepresentedBy`), `exists_simplicialHomRepresentation`, `simplicialHomRepresentation`,
`simplicialHomObject` and `SimplicialHomRepresentation.homEquiv`. The node's "any pair
representing F_{S,K}, with universal object" is now the uniquely characterising predicate
`(simplicialHomFamilyFunctor K S).IsRepresentedBy u` on a pair `(H, u)`; existence stays the
landed lemma. The restriction morphism is `simplicialHomRestriction A u hu'`, the preimage of
`u.restrict A` under the bijection of `hu'` (no sorry data). The record's main declaration is
`simplicialHomFamilyFunctor`. Citers bind `(H) (u : SimplicialHomFamily K S H)
(hu : (simplicialHomFamilyFunctor K S).IsRepresentedBy u)`.
