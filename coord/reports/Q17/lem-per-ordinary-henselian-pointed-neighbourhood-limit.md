## Worker report

The module `Sheaf.AlgebraicGeometry.OrdinaryHenselianPointedNeighbourhoodLimit` states
`AlgebraicGeometry.exists_ordinary_henselian_pointed_neighbourhood_limit`. Its only theorem
has proof `sorry`; no definition or auxiliary theorem is added. The original statement,
statement dependencies, and proof are unchanged. Q36's existing completion is the stage-1
split and review, not a Lean statement: the current node has no Lean record. This delivery
supplies stage 2 on top of that split.

I read the node and all seven statement dependencies, their recorded declarations and source
docstrings, the stage-2 brief and error list, and Stacks `algebra.tex`, Tag 04GN
(`lemma-henselization`), including its pointed-pair proof. The module docstring reproduces
all eight steps of the node's proof, including the direct construction over A rather than
the false assertion that A → A_p is étale.

Clause-by-clause correspondence:

- A commutative ring and its chosen prime/point are `(A : Type u) [CommRing A]`
  and `(x : Spec (CommRingCat.of A))`. The prime is `x.asIdeal`. No local,
  Noetherian, reduced, or separably closed hypothesis is imposed on A.
- The nonempty directed set is the existential `I : Type u`, `Preorder I`,
  `Nonempty I`, and `IsDirected I (· ≤ ·)`. This uses the standing directed-set convention.
- The system of commutative A-algebras is `F : I ⥤ Under (CommRingCat.of A)`.
  An object is exactly a ring with a structural homomorphism from A, and an arrow is a
  homomorphism commuting with the structural maps. Functoriality provides the system laws.
- The colimit H is `c.pt.right`, its structural map is `c.pt.hom`, its canonical legs are
  `(c.ι.app a).right`, and `Nonempty (IsColimit c)` supplies the colimit universal property
  in A-algebras. The existential `hH : HenselianLocalRing c.pt.right` supplies both locality
  and henselianness; `letI := hH` makes its maximal ideal and closed point available.
- Each neighbourhood is `Spec.map (F.obj a).hom`. The five conjuncts in the first `∀ a`
  give separatedness, étaleness, and finite presentation in precisely the convention of
  `def-weil-pbc-scheme-conventions`: locally of finite presentation, quasi-compact, and
  quasi-separated. Affineness is built into its source and target.
- The chosen point is `xa a`. The second `∀ a` supplies the equality of its image with x.
  Its residue isomorphism is `e a`, and the equation in that conjunct says its forward map
  is exactly the induced `Scheme.Hom.residueFieldMap`, after transport along the point
  equality. Thus an unrelated abstract isomorphism cannot satisfy the conclusion.
- For each transition `f : a ⟶ b`, the next conjunct says its spectrum map sends `xa b`
  to `xa a`. Its equation is the commutative square of residue identifications: first
  `(e a).hom`, then the induced transition residue map, equals `(e b).hom`. The inserted
  `eqToHom` only transports the source along the specified point equality.
- The next `∀ a` says the canonical projection `Spec H → Spec A_a` sends
  `IsLocalRing.closedPoint H` to `xa a`.
- The local map A_p → H is the existential ring homomorphism `g` from
  `Localization.AtPrime x.asIdeal`, with `IsLocalHom g`. Its composite with the canonical
  localization homomorphism is required to equal the actual structural map `c.pt.hom.hom`.
  It is therefore an extension of the given A-algebra structure, not an arbitrary local map.
- `x.asIdeal.map c.pt.hom.hom = IsLocalRing.maximalIdeal c.pt.right` is pH = m_H.
- The existential `eH` is the isomorphism κ(x) → H/pH. The equation says its composite
  with A → κ(x) is A → H → H/pH. Here the canonical comparison
  `Scheme.Spec.residueFieldIso` identifies the scheme residue field with
  `x.asIdeal.ResidueField`; no second definition of residue field is introduced.
  Since κ(x) is the fraction field of A/p, this compatibility determines the canonical
  induced field map, including when p is nonmaximal.
- The final clause quantifies over every scheme `T : Scheme.{u}`, its map t to `Spec A`,
  and compatible legs π. The first hypothesis says each leg is over `Spec A`, the second
  is its compatibility with every transition. `∃! g` gives its unique factorization through
  `Spec H`, both over `Spec A` and with each required projection. This is the limit
  universal property in schemes over `Spec A`, including the specified projections.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and `Scheme.Spec.residueFieldIso`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: the recorded henselian-terminology
  interface, which imports Mathlib's `HenselianLocalRing`. This class extends `IsLocalRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- The convention dependency has no module of its own. Its named Mathlib declarations
  `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`, and `QuasiSeparated` are
  used inline, with the stated finite-presentation conjunction.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone` and `IsColimit`. Choosing a colimit
  cocone rather than a particular `colimit F` retains exactly the universal property.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`; residue fields
  of primes use the recorded `Ideal.ResidueField` from the imported residue-field module.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `Under`, its objects, and its morphisms,
  the existing category of commutative A-algebras. No new system or algebra notion is defined.

The available recorded proof interfaces are imported privately:
`Sheaf.RingTheory.EtaleResidueTriplesFiltered`,
`Sheaf.RingTheory.EtaleResidueTripleUnitRefinement`,
`Sheaf.RingTheory.EtaleResidueTripleIdealRefinement`,
`Sheaf.RingTheory.FilteredColimitFiniteData`,
`WeilConjectures.RingTheory.HenselianLocalRootLifting`, and Mathlib's affine étale site.
The remaining proof nodes have no recorded project module, or are elementary/Mathlib
interfaces already supplied by these imports; they are retained in the DAG. There is no
import cycle and no proof-only hypothesis has entered the signature.

Edge cases checked:

- A field with x = (0): H can be the field itself; no separable closure is forced.
- A = ℤ and x = (0): A → κ(x) need not be surjective. The signature uses A_p and the
  canonical residue comparison, and does not falsely call A → A_p finitely presented.
- Nonmaximal primes in a nonlocal A are allowed. The stage primes need not be maximal;
  only H's designated point is required to be its closed point.
- A nonreduced ring, e.g. k[ε]/ε², and non-Noetherian A: no forbidden assumptions occur.
- The zero ring has no x in its spectrum; the statement correctly has no instance there.
- The index cannot be empty. Quantification over arbitrary T in the limit clause includes
  the empty scheme. Identity transitions and their residue squares are included.
- All ring and scheme carriers lie in the arbitrary universe u. The henselization and a
  small directed indexing system can be constructed in the same universe as A (finite
  presentations and their finite diagrams form a set there). This excludes no A. All
  universes and binders are explicit, with `set_option autoImplicit false`.

Searches made during this attempt:

- `msearch.py leanfinder`, query "An ordinary henselization at a prime is a directed
  colimit of affine etale neighbourhoods with unchanged residue fields": eight hits,
  including `Algebra.IsEtaleAt`, `HenselianLocalRing`, standard étale localization and
  `Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime`.
  These provide local criteria or a single neighbourhood, not the asserted system.
- `msearch.py loogle`, query `"HenselianLocalRing", "Algebra.Etale"`: zero hits.
- `msearch.py grep`, query `henselization|Henselization`, subdirectory `RingTheory`:
  zero Mathlib hits.
- `msearch.py leansearch`, query "An ordinary henselization is a directed colimit of
  pointed etale algebras with unchanged residue field": eight hits, headed by
  `RingHom.Etale`, `HenselianLocalRing.TFAE`, and `Algebra.Etale.formallyEtale`.
  No theorem supplies this statement.
- `rg` on upstream `WeilConjectures` for the exact item id: no hit. Searching upstream
  and `lean/Sheaf` for ordinary henselization, `OrdinaryHensel`, and residue-preserving
  terminology found the universal property, ind-étaleness, local-pair comparison and
  strict-henselization results. None supplies the residue-preserving directed system
  and its full inverse-limit conclusion. The existing finite-flat exchange module
  mentions this node only in its proof docstring.

No new nodes, dependency repairs, statement correction, or statement dispute is needed.
Compilation uses only the prescribed `scompile.py` wrapper. The first compile found the
residue comparison's missing `Scheme` namespace; it was corrected. The resulting module
compiled cleanly in both sandbox and library modes; no errors or non-sorry warnings remain.

## Second reading by Q17

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
