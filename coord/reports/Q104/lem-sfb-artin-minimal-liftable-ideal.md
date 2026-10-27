## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinMinimalLiftableIdeal` states
`AlgebraicGeometry.ArtinDeformation.exists_isLeast_liftableIdeal`, with proof `sorry`.
It also defines `IsLiftableIdeal`, the literal predicate from the item's statement.
There is no statement correction or disputed claim. The only item fields changed
are `lean` and the addition of the new canonical-quotient node to `stmt_deps`.

Clause-by-clause correspondence:

- Commutative Noetherian R: `{R k : Type u} [CommRing R] [IsNoetherianRing R]`.
- A finite type R-field k: `[Field k] [Algebra R k] [Algebra.FiniteType R k]`.
  Finite type here means finitely generated as an R-algebra, the affine formulation
  of the recorded finite-type morphism definition. It is not a finite-extension
  hypothesis. These parameters follow the recorded test-category interface.
- Marked Artinian local R-algebras, and local residue-preserving maps:
  `{B A : TestCategory R k} (f : B ⟶ A)`. The recorded full subcategory of
  augmented R-algebras retains exactly this marking; it automatically makes maps local.
- A predeformation category satisfying (RS):
  `(F : CofibredGroupoids.{u, v, w} R k) (hF : IsPredeformation F)
  (hRS : IsRimSchlessinger F)`. All three universes are explicit; fibre objects
  and morphisms retain both universes of the dependency interface.
- Surjectivity of B to A: `(hf : Function.Surjective (map f))`.
- I is its kernel: written directly as `RingHom.ker (map f).toRingHom` everywhere,
  rather than adding an arbitrary ideal with a redundant equality to the kernel.
- The maximal ideal annihilates I: `hI` quantifies over every b in
  `IsLocalRing.maximalIdeal (ring B)` and every t in that kernel and states `b * t = 0`.
  No one-dimensional or nonzero-kernel condition is imposed.
- The object x over A: `(x : fibre F A)`.
- L is an ideal contained in I: `IsLiftableIdeal` first requires
  `∃ hL : L ≤ RingHom.ker (map f).toRingHom`.
- An object y over B/L: `∃ y : fibre F (testQuotient f L hL)`.
  This is the literal ring quotient with its induced residue marking, not an
  arbitrary quotient presentation or chosen object of the test category.
- Restriction to A is isomorphic to x:
  `Nonempty ((push F (testQuotientTo f L hL)).obj y ≅ x)`.
  The existential isomorphism is exactly the source's isomorphism, with covariant
  transport along the canonical B/L to A arrow.
- Leastness and liftability: `∃ L, IsLeast {J | IsLiftableIdeal F f x J} L`.
  The membership component of `IsLeast` asserts that this L is itself liftable;
  its order component says L is contained in every liftable J. This is leastness,
  not merely minimality.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ArtinDeformationTestCategory`:
  `AlgebraicGeometry.ArtinDeformation.TestCategory`, `ring`, `map`, `residue`,
  `IsTestAlgebra`, `CofibredGroupoids`, `fibre`, `push`, `IsPredeformation`,
  `IsRimSchlessinger`. I read the full source including augmentation conditions,
  pseudofunctor transport, fibre-product comparison and (RS).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`. I also read the recorded
  scheme predicates `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
  `AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
  The present node concerns rings, so the already imported affine algebra
  predicate is used without a duplicate finite-type notion.
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.liftₐ` builds
  the actual quotient algebra map with the actual kernel-containment proof.
- Proof-only imports: `Mathlib.LinearAlgebra.Basis.VectorSpace` for
  `Submodule.exists_isCompl`, and `Mathlib.RingTheory.HopkinsLevitzki` for
  `isArtinianRing_iff_isFiniteLength`, exactly the two Mathlib proof dependencies.
- New definition dependency `def-sfb-artin-test-quotient`:
  `Sheaf.AlgebraicGeometry.ArtinDeformationTestQuotient`, declarations listed below.

The theorem docstring contains every proof step: nonemptiness and upward closure;
complementary enlargement; the actual quotient fibre-product isomorphism;
essential surjectivity under (RS); finite-length minimality and intersection
leastness. I read Stacks `formal-defos.tex`, lemma-largest-closed-where-lift
(Tag 06SZ), lines 3834 onward. Its displayed A/(J intersect K) formula has the
inherited typo for B/(J intersect K), noted in the accepted split and docstring.
This affects neither the node's statement nor its Lean rendering.

Edge cases checked before finalizing the statement:

- I=0: no small-extension/nonzero hypothesis excludes identity extensions.
  The only candidate L is zero; B/0 is canonically B and hence A.
- x already lifts to B: zero is an allowed liftable ideal and is the least ideal.
- L=I: B/I is canonically A, so the liftable set is nonempty.
- General nonzero socle kernel: no principal or one-dimensional restriction.
- Dual numbers over k: both zero and the full kernel are legitimate candidates;
  the assertion accommodates an obstruction requiring the full kernel.
- J=K, J=I or K=I, and J+K strictly less than I: these cases are covered by the
  complement argument rather than assuming the quotient fibre-product identity
  for arbitrary J+K.
- The quotient construction needs no surjectivity of f: any test arrow preserves
  the marked residues, so L inside its kernel is inside the maximal ideal of B.
  In particular L cannot be the improper ideal, and B/L is a nonzero local ring.
- Fibre groupoids may be empty away from the supplied x; liftability remains an
  existence predicate, not a nonemptiness hypothesis on all fibres.

Searches made (all on 2026-10-24):

1. `msearch.py leanfinder`: “A predeformation groupoid satisfying Rim Schlessinger
   has a least ideal in a socle extension allowing a lift”: 8 hits, all formal
   smoothness/extension lifting; none states the deformation-object assertion.
2. `msearch.py loogle`: `"Schlessinger"`: 0 hits.
3. `msearch.py grep`: `minimalLiftable|liftableIdeal|Schlessinger|predeformation`:
   0 Mathlib hits.
4. `msearch.py leansearch`: “Quotient of a marked Artinian local algebra with
   specified residue field is a marked test algebra”: 8 hits concerning ordinary
   local quotients, residue fields and finite-type quotients, not the marked category.
5. `msearch.py leanfinder`: “canonical quotient of augmented Artinian local
   algebra by ideal in augmentation kernel with induced residue map”: 8 hits
   concerning cotangent spaces, residue fields and extension quotients; no match.
6. `msearch.py grep`: `quotientTest|testQuotient|IsTestAlgebra`: 0 Mathlib hits.
7. `msearch.py loogle`: `Ideal.Quotient.liftₐ`: 3 hits, the map and its application
   and composition lemmas. This map is reused in the new construction.
8. `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
   for the least-ideal and marked-quotient names found no match. A broader search
   for `Schlessinger|predeformation` found the recorded test-category module and
   distinct scheme-stack (RS) interfaces, not the present statement.
9. `rg` for this item's blueprint id under `lean/WeilConjectures`: no match.
10. DAG search for marked Artinian quotient constructions and the proposed new id:
    no existing notion. `tools/blueprint_refs.py search 'quotient test'`: 0 nodes;
    search 'Artinian': 2 unrelated coefficient/perfect-complex blueprint nodes.

All compiles use scompile.py. Both modules compiled individually in dependency
order. The first compile found one unused binder in a quotient-map lambda; it
was replaced by `_`. No global build or direct repository write was performed.

## New nodes

`def-sfb-artin-test-quotient` defines the canonical marked test B/L and map B/L to A
for any test arrow f and L contained in its kernel. Source: Tag 06SZ's literal
quotients in the definition of the liftable set. Searches above and the new node's
`mathlib_searches` found no existing marked quotient in this category. The existing
complete-local truncations in `ArtinDeformationTestCategory` only handle powers of
a complete local ring's maximal ideal and do not give this arbitrary ideal quotient.

The module `Sheaf.AlgebraicGeometry.ArtinDeformationTestQuotient` declares
`quotientToAlgebra`, `testQuotientResidue`, `testQuotient_isTestAlgebra`,
`testQuotient`, and `testQuotientTo` in `AlgebraicGeometry.ArtinDeformation`.
The algebra map is `Ideal.Quotient.liftₐ`, the augmentation is its composite with
the target's actual residue map, and the test arrow is the full-subcategory lift
of that map. There is no arbitrary chosen map or hollow data definition.
The only postponed theorem is the named proof obligation
`testQuotient_isTestAlgebra`, whose complete natural-language proof is in its
docstring and whose assertion is part of the new definition node's statement.

## Second reading by Q104

I reread the completed files against the two node statements, checking the
kernel-containment existential, the direction of covariant transport, and both
components of `IsLeast`. They match every hypothesis and clause listed above.
For the quotient node, the underlying type is literally `ring B ⧸ L`, its residue
is `[b]` mapped to the residue of f(b), and the arrow is `[b]` mapped to f(b).
The auxiliary proof obligation supplies only local/Artinian/marking proofs;
it does not select any data. No hypothesis was added and no conclusion dropped.
The initial generated JSON signature for `testQuotient` accidentally matched the
longer name `testQuotientResidue`; this was corrected to the exact `testQuotient`
signature before preflight. The unused lambda binder was also corrected.
This is a separate self-review pass; no independent agent was started, as the
worker brief explicitly prohibits other agents. The maintainer's independent
review reads the delivery.

Preflight metadata repair: the current server checker additionally requires
`import_flags` on new definition nodes (the written brief's field list omitted
it). The new node now carries the empty list, since it has no import flags.
