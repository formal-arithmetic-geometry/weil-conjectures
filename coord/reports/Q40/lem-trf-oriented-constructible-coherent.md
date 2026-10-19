## Worker report

The module states `AlgebraicGeometry.orientedConstructible_iff_coherent`, with proof
`sorry`. The DAG statement is unchanged. No new notions or nodes are needed. A named public instance supplies the standard
Mathlib coproducts of set sheaves; it is data constructed by the existing
`Sheaf.instHasColimitsOfShape` using `HasSheafify.isRightAdjoint` directly.
This avoids recursive typeclass search for the sheafification adjunction.

Hypotheses and conclusion, clause by clause:

- Schemes and their morphism are `{X S : Scheme.{u}}` and `(f : X ⟶ S)`.
- Noetherianity of S is `[IsLocallyNoetherian S] [CompactSpace S]`, exactly the
  locally Noetherian and quasi-compact conditions in the node.
- Finite presentation is `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`, the three conditions required by the recorded conventions.
- The finite commutative coefficient ring is `(Λ : Type v) [CommRing Λ] [Finite Λ]`.
- `(F : Modules.{u, v} f (𝟙 S) Λ)` is a sheaf of modules over the constant coefficient
  ring on the left oriented product with second map the identity. This is precisely the
  vanishing topos presentation specified by the constructibility dependency. Its common
  site/coefficient universe is `max (u + 1) v`, with no equation between u and v.
- `IsConstructible f (𝟙 S) Λ F` uses the recorded finite constructible locally closed
  stratifications and locally constant finite module values; it does not introduce
  an alternative constructibility predicate.
- `SheafOfModules.toSheaf` forgets F to its actual sheaf of abelian groups;
  `sheafCompose ... (forget AddCommGrpCat)` then forgets only the group operations.
  Thus the object on the right is |F|, not F in the additive category.
- `IsCoherentObject.{max (u + 1) v}` is exactly the recorded quasi-compact and
  quasi-separated object predicate, in the set-valued oriented-product topos.
- The connective is `↔`, giving both directions with no added conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no separation assumption).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `.QuasiCompact`, and
  `.QuasiSeparated`: `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated`.
- `Sheaf.Paper.OrientedNearbyCycles`: `EtaleSite`, `etaleBaseChange`, `Coeff`,
  `VanishingSite`, `vanishingTopology`, `VanishingTopos`, and `vanishingDatum`.
- `Sheaf.Paper.OrientedConstructibleSheaf`: `ProductSite`, `productTopology`,
  `Modules`, `stratumRestriction`, and `IsConstructible`. Its docstring explicitly
  identifies the specialization b = identity with the recorded vanishing topos.
- `Sheaf.CategoryTheory.Sites.CoherentTopos`: `IsQuasiCompactObject`,
  `IsQuasiSeparatedObject`, and `IsCoherentObject`.
- `Mathlib.CategoryTheory.Limits.Types.Colimits` supplies colimits of types;
  `CategoryTheory.Sheaf.instHasColimitsOfShape` supplies their sheafified colimits.
- Mathlib `SheafOfModules.toSheaf` and `CategoryTheory.sheafCompose` provide the
  underlying set sheaf directly; no helper or copied definition is introduced.

The set-valued proof dependency `lem-trf-coherent-set-criterion` has no Lean record
in the DAG inspected. It is used in the natural-language proof docstring, and its
module import will be added by the maintainer when that statement is landed.
The stated proof dependencies for constructibility and nearby cycles are already
publicly available through the statement imports.

Edge cases checked mathematically: X empty and S empty allow empty stratifications
and the degenerate topos, without any nonemptiness assumption. The zero module is
included (its underlying set sheaf is terminal); the zero coefficient ring is
included, with its unique modules. On a geometric point the criterion reduces to
finiteness of the underlying module set, so an infinite constant module is excluded
by both sides. No characteristic or invertibility hypothesis is added. Arbitrary
finite rings and independent scheme/coefficient universes are retained.

Searches actually run:

- msearch leanfinder: “A finite module sheaf on a vanishing topos is constructible if
  and only if its underlying sheaf of sets is coherent”. Eight hits: condensed-module
  discreteness, finite-type/quasicoherent module sheaves, and constant condensed
  modules. None states the oriented-product coherence criterion.
- msearch loogle: `IsCoherentObject, IsConstructible`. No hits; the Mathlib service
  reports unknown identifier IsCoherentObject (the predicate is in this project).
- msearch grep: `coherent.?object|oriented.?constructible|vanishing.?topos`.
  No Mathlib matches.
- msearch leansearch: the same natural-language criterion. Eight hits concerning
  finite type, finite presentation, and quasicoherent module sheaves; no match.
- rg in upstream WeilConjectures for the item id and coherence/constructibility
  combinations, and rg in dag/lean_names_upstream.json for the proposed declaration
  and IsCoherentObject: no exact statement or name collision.
  The helper instance name was also searched in Mathlib and both project libraries,
  with no name collision.
- rg in lean/Sheaf for IsCoherentObject and oriented constructibility found the
  dependency definitions read above, but no theorem identifying the two predicates.

Source read online: Orgogozo, author draft §7.1 (printed p. 16), defines finite
constructible stratifications and finite locally constant restrictions. Section 8.1
(printed pp. 17–18) extends this to sets and modules, proves coherence for
constructible set sheaves, and identifies constructibility and coherence in these
topoi. The finite-module direction refines constant-set charts for finitely many
module operations as expanded in the DAG proof. The module docstring records all
three proof steps and the initial-chart case.

Source URL: https://www.cmls.polytechnique.fr/perso/orgogozo/articles/Modifications%20et%20cycles%20proches%20sur%20une%20base%20g%C3%A9n%C3%A9rale.pdf

WANTED: a local archival copy of the Orgogozo author draft in literature; only the
online copy was read. No statement correction or disputed statement was needed.

Validation: the final module compiles through the prescribed per-file scompile.py
and deliver2.py wrappers, with the single expected sorry and no other warning.
The delivery dry run performs the maintainer preflight before pushing.

## Second reading by Q40

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
