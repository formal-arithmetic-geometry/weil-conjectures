## Worker report

Reused the existing declaration `ModuleCat.idealPowerTorsion_rightDerived_iso_cech`
in `Sheaf.Algebra.Homology.IdealTorsionCechComputation`, already attached to
`lem-per-ideal-torsion-cech-computation` and independently reviewed for Q146.
No module is written and no theorem is proved. Only the item's `lean` field changes.
The existing theorem and its complete explicit complex were read, together with
its live source obtained through `scompile.py --source`, both statement dependencies,
and Stacks `dualizing.tex`, Tag 0956 (`lemma-compute-local-cohomology-noetherian`).

Clause-by-clause correspondence:

- The commutative Noetherian ring A is `{R : Type u} [CommRing R]
  [IsNoetherianRing R]`. The ring universe is explicitly bound in the owning module.
  `IsNoetherianRing` says that every ideal is finitely generated.
- The integer r >= 0 and list f_1,...,f_r are `(r : ℕ) (t : Fin r → R)`.
  The ideal I=(f_1,...,f_r) is `Ideal.span (Set.range t)`. The node introduces I
  by this equality, so no separately quantified arbitrary ideal is lost.
- Every module M is quantified by `∀ M : ModuleCat.{u} R`, with no finite-generation,
  nonzero, torsion, or other condition. This is precisely the module universe of
  the recorded dependency `ModuleCat.idealPowerTorsion`.
- H_I^j(M)=R^j Γ_I(M) is
  `((idealPowerTorsion (Ideal.span (Set.range t))).rightDerived q).obj M`.
  This uses the actual recorded ideal-power torsion functor, not the unrelated
  Ext-colimit definition `localCohomology`.
- The complex is `IdealTorsionCech.complex t M`, built by `CochainComplex.of`.
  Its `term t M 0` is definitionally M. Its positive degree p term is the
  module of functions from `Fin p ↪o Fin r` to
  `LocalizedModule.Away (tupleProduct t s) M`: exactly the finite product over
  strictly increasing p-tuples, localized at powers of the indicated product.
  There are no such tuples for p>r, so those terms are zero modules. The
  nonnegative complex represents the extension by zero in negative degrees;
  its degree-zero homology has incoming image zero.
- `differential t M 0` is the family of `LocalizedModule.mkLinearMap` maps,
  sending m to m/1. Higher differentials sum over omitted positions a using
  `Fin.succAboveOrderEmb a`, the canonical `localizationMap` along divisibility,
  and the integer coefficient `(-1 : ℤ)^a.val`. Positions start at zero in Lean,
  so this is the node's sign (-1)^(a-1) for one-based position a. The existing
  `differential_sq` supplies the cochain identity. The canonical localization
  map is chosen from a unique characterization on numerators, not arbitrary data.
- Every j>=0 is `(q : ℕ)`. The theorem provides a family of isomorphisms in
  `ModuleCat R` between R^qΓ_I(M) and `(complex t M).homology q`; hence these are
  R-linear isomorphisms. Taking their inverses gives exactly the orientation
  H^q(C) ≅ H_I^q(M) displayed in this item, without an extra hypothesis or clause.
- Naturality is the full equation for every module morphism f:M→N:
  `rightDerived.map f ≫ (e N).hom = (e M).hom ≫ homologyMap (map t f) q`.
  `map t f` sends each fraction m/u to f(m)/u and is f in degree zero.
  Composing this equation with `(e M).inv` and `(e N).inv` gives naturality
  in the item's opposite orientation as well.
- For r=0 the generator range is empty, its span is zero, and every positive
  degree index set is empty. Thus the complex is M in degree zero only,
  exactly the node's final clause; no nonempty-list hypothesis is present.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the recorded Mathlib
  match of `def-weil-pbc-noetherian-ring` (its full docstring and abbreviation read).
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`:
  `ModuleCat.idealPowerTorsion` and its additive instance, the recorded declarations
  of `def-sbc-ideal-power-torsion-functor`. Its objects are
  `Ideal.primaryComponent M I`, namely elements killed by some ideal power.
- `Sheaf.Algebra.Homology.IdealTorsionCechComputation`:
  `ModuleCat.IdealTorsionCech.term`, `tupleProduct`, `localizationMap`,
  `differential`, `complex`, `map`, and the comparison theorem recorded above.
  These are reused in place, without introducing another definition node.

Edge cases checked mathematically against the explicit definitions: r=0 as above;
q=0 gives the kernel of M→∏M_f; a zero generator localizes the corresponding factors
at zero and contributes zero modules; a unit generator contracts the localization
complex and gives zero torsion cohomology; the zero ring and zero module are allowed;
repeated generators do not change the increasing-position construction. Arbitrary
modules, including infinitely generated ones, are included. No statement fault or
STATEMENT-DISPUTED issue was found.

Searches performed:

- `msearch.py leanfinder`: "For a Noetherian ring the cohomology of the extended
  alternating localization Cech complex is naturally isomorphic to the right
  derived ideal power torsion functor". Eight hits: localCohomology, its radical
  comparisons and diagram constructions, and adic-completion comparisons; none
  is this theorem.
- `msearch.py loogle`: `localCohomology`. Three hits: the Ext-colimit definition
  and its two radical comparison isomorphisms; no Cech computation.
- `msearch.py grep`: `localCohomology|[Cc]ech|torsion`, `Algebra/Homology`.
  Five hits in Mathlib's LocalCohomology.lean; its Future work explicitly lists
  both right-derived-torsion and Cech comparisons as unfinished.
- `rg` in upstream WeilConjectures for the item id and in its Algebra/Homology
  directory for localCohomology/Cech/idealPowerTorsion: no matching declaration.
- `rg` in project lean/Sheaf for the item id and Cech/torsion comparisons found
  `IdealTorsionCechComputation.lean`. Opened the entire file, its node and its
  passed stage-2 review; it states exactly this item's Tag 0956 assertion.

The previous attempt confused the stage-1 Q02 merge at ledger line 41832 with
stage-2 completion. The item has a reviewed split but no Lean record on the
starting base. This delivery supplies that missing record using the exact
already-landed duplicate theorem, as required by the one-definition rule.
The existing comparison theorem's proof docstring cites this item; this is the
already-reported duplicate DAG interface, not an import cycle introduced here.
The item's independent proof plan through the adjoint Cech model and Noetherian
comparison remains unchanged and is the route for proving the shared declaration.
Maintainer consolidation of the duplicate nodes can use this shared binding.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
