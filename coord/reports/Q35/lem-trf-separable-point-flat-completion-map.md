## Worker report

The module `Sheaf.RingTheory.SeparablePointFlatCompletionMap` states
`SeparablePoint.flat_completion_map`, with `sorry`, and names the particular evaluation,
prime, local rings, completions, extended ideals and structural K-map used in that statement.
All auxiliary data are actual constructions from Mathlib, with no choice of an unspecified
map and no postponed theorem used to construct them. No new DAG notion is needed: these
helpers are the objects explicitly introduced by this node. All ten declarations are recorded
in `lean.declarations`. No statement correction or disputed assertion was needed.

I read the complete item and every statement dependency, their recorded declarations and
Mathlib matches, and the signatures/docstrings in the actual source modules. I also read the
proof dependencies and available interfaces. Sources checked: Stacks `varieties.tex`,
`lemma-base-change-complete-local-ring` (0C54), including the coefficient square and the
flat-completion paragraph; the referenced change-of-fields results 0C4Y/0C4Z/0C50 and the
recorded 0C4G completion interface. The current blueprint ancestry in the node concerns the
completion comparison below the nodal-family branch; this delivery changes no blueprint route.

Hypotheses and objects, matched in full:

- The fields k and K are independent universe parameters `Type u`, `Type w` with `Field`
  instances; `Algebra k K` is the field extension, whose structural map is automatically
  injective. S is `Type v` with `CommRing S`, `Algebra k S`. No equality of universes or
  restriction to algebraic K/k is imposed.
- Finite type over k is the explicit hypothesis
  `hfiniteType : (algebraMap k S).FiniteType`, exactly the recorded `RingHom.FiniteType`.
- The ideal p is `Ideal S` with `[p.IsMaximal]`. Its residue field F is literally `S ⧸ p`,
  with Mathlib's quotient field/algebra structures. F/k finite is `[Module.Finite k (S ⧸ p)]`;
  separable algebraic is `[Algebra.IsSeparable k (S ⧸ p)]`.
- The selected k-embedding is `iota : (S ⧸ p) →ₐ[k] K`; injectivity follows for any unital
  homomorphism from this field. No extra extension structure on K over F is chosen.
- The tensor product is Mathlib's `S ⊗[k] K`. `evaluation p iota` is the actual tensor lift of
  `iota.comp (Ideal.Quotient.mkₐ k p)` and `AlgHom.id k K`; therefore on a pure tensor it is
  exactly `iota (s mod p) * lambda`. `point p iota` has ideal the literal kernel of this map.
  Its prime witness is Mathlib's unconditional theorem for kernels into domains.
- `Source p` is `Localization.AtPrime p`, and `Target p iota` is localization at that exact
  evaluation kernel. Their local ring structures are Mathlib instances, so locality of A and
  B is present directly in their types and does not have to be assumed in the theorem.
- m and n throughout the signature are `IsLocalRing.maximalIdeal (Source p)` and
  `IsLocalRing.maximalIdeal (Target p iota)`. The two ideal-map equalities in the first block
  identify these with pA and qB, respectively, as required.
- `SourceCompletion p` and `TargetCompletion p iota` are literally `AdicCompletion m A` and
  `AdicCompletion n B`, Mathlib's compatible-sequence inverse limits. Their A/B-algebra maps
  are the canonical completion maps.

Conclusions, matched in full:

- `(point p iota).asIdeal.IsMaximal` states maximality of q. The next two
  `IsNoetherianRing` clauses state Noetherianity of A and B. Locality is provided by the
  canonical localization instances noted above.
- `ringKrullDim (Source p) = ringKrullDim (Target p iota)` is the claimed dimension equality.
- The existential `g : Source p →ₐ[k] Target p iota` is a k-algebra map, required to be
  `g.toRingHom.Flat` and `IsLocalHom g`. It is characterized on EVERY fraction s/d by
  `g(s/d) * (d tensor 1) = s tensor 1` in B. The second factor is a unit since d is outside p
  and its evaluation is the nonzero image of its residue under iota. Thus this is exactly the
  displayed fraction formula, without making an arbitrary choice of a fraction denominator
  in the target. Fractions exhaust A, so it uniquely determines g.
- `(maximalIdeal A).map g.toRingHom = maximalIdeal B` is mB=n.
- `piA : A →ₐ[k] S ⧸ p` and `piB : B →ₐ[k] K` are surjective with kernels m and n.
  Their values on the original rings are respectively reduction mod p and `evaluation`.
  As every element is a fraction with a unit denominator, these equalities uniquely specify
  the canonical residue maps and exhibit the required residue field identifications F,K.
- R,C are each `IsNoetherianRing` and `IsLocalRing`. `sourceCompletedIdeal` is m mapped by
  the canonical A→R map; `targetCompletedIdeal` is n mapped by B→C. Both are asserted
  `IsMaximal`, so locality identifies them with the maximal ideals of R,C. This states
  precisely m_R=mR and m_C=nC without requiring a chosen proof of locality in the signature.
- The two `IsAdicComplete` clauses are completeness for those very extended maximal ideals,
  as rings over themselves, including Hausdorffness.
- `h : R →ₐ[k] C` is required to be flat and local. The explicit `@Continuous` clause
  equips R and C with the adic topologies of m_R and m_C, respectively.
- The `forall r x a` implication specifies h at EVERY quotient level r: whenever the rth
  projection of x is a mod m^r, the rth projection of h(x) is g(a) mod n^r. Each projection
  has representatives, and the projections jointly separate points, so this determines the
  actual induced completion map, not an unconstrained flat map. It also implies its
  compatibility with the canonical A→R and B→C maps. Including r=0 is harmless and valid.
- `(sourceCompletedIdeal p).map h.toRingHom = targetCompletedIdeal p iota` is m_R C=m_C.
- `piR : R →ₐ[k] F` and `piC : C →ₐ[k] K` are surjective, with kernels m_R and m_C.
  The two `evalOneₐ` implications identify them with the canonical first projections followed
  by piA/piB. Every first projection has a representative, so these maps are uniquely
  specified; the associated quotient isomorphisms give exactly residue fields F and K.
- `piC.comp h = iota.comp piR` says that the residue map of h is iota.
- `coefficientMap p iota` is the actual composite K→S tensor_k K→B→C, using
  `Algebra.TensorProduct.includeRight` and the canonical localization/completion algebra
  maps. It is tau, not an arbitrary coefficient embedding. The clause
  `piC.comp (coefficientMap p iota) = AlgHom.id k K` records its residue identity.
- The last universal quantifier includes EVERY k-algebra map sigma:F→R satisfying
  `piR.comp sigma = AlgHom.id k F`. Its conclusion is the required exact equality
  `h.comp sigma = (coefficientMap p iota).comp iota`.

Dependency declarations used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType` (and its Algebra interface).
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, through the public import
  `Mathlib.RingTheory.TensorProduct.Maps`, which also supplies the canonical algebra lift.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, local instances.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`, `IsAdicComplete`,
  canonical algebra maps, `evalₐ`, `evalOneₐ`. The algebra module publicly imports Basic.

Available proof dependencies are imported privately as required:
`Sheaf.RingTheory.EtaleHenselianRingLift` (`AlgebraicGeometry.Scheme.etale_henselian_ring_lift`),
`WeilConjectures.RingTheory.AdicCompletionNoetherian` (`AdicCompletion.isNoetherianRing`),
`Mathlib.RingTheory.Henselian` (`IsAdicComplete.henselianRing`),
`Mathlib.AlgebraicGeometry.Morphisms.Etale` (the etale `HasRingHomProperty.Spec_iff` interface),
`WeilConjectures.Mathlib.RingTheory.Etale.Field` (`Algebra.Etale.of_finite_of_isSeparable`),
`WeilConjectures.RingTheory.FlatCompletion` (`flat_adicCompletion_of_flat_local`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
`Mathlib.RingTheory.AdicCompletion.LocalRing` (locality, maximal-ideal and residue lemmas),
and `Mathlib.RingTheory.RingHom.FaithfullyFlat`. Completion completeness is provided by
`.AdicCompletion.Completeness`, imported through LocalRing. The proof dependency
`lem-trf-separable-evaluation-local-base-change` currently has no recorded declaration or
Mathlib match; it is not a statement dependency and no import for it is invented.
The theorem docstring carries all six proof steps and their named dependencies.

Edge cases checked before writing: S=F a finite separable field (both maximal ideals zero,
A=F and B=K and the completion maps reduce to iota); a rational point of k[t] with K/k
transcendental; the nonreduced ring F[t]/(t^2); identity field extension K=k when an embedding
exists; positive characteristic and a nontrivial finite separable F/k. No reducedness,
integrality or characteristic-zero assumptions occur. A zero S admits no maximal ideal,
so does not give omitted input data. The full quantifier over sigma remains even if the
section is not supplied separately. The inseparable case is properly excluded: it can make
the localized closed fibre nonreduced, breaking mB=n. Independent universes u,v,w are retained.

Searches made with `msearch.py`:

- LeanSearch: "A finite separable closed point after field extension induces a flat local
  completion map compatible with every coefficient field section" returned eight hits on
  separable extensions and formal etaleness, including `Algebra.FormallyEtale.of_isSeparable`;
  none states the complete map or section compatibility.

- LeanFinder: "Finite separable closed point field extension flat completed local ring map
  compatible coefficient fields" returned eight ingredient results, including
  `Algebra.FormallyUnramified.iff_map_maximalIdeal_eq`, residue-field separability and
  local unramified statements. None gives the full completion theorem or its coefficient
  section compatibility.
- Loogle: `AdicCompletion, Algebra.IsSeparable` returned zero hits.
- Mathlib grep: `map|eval|continuous` in `RingTheory/AdicCompletion` returned the expected
  completion projections, module functoriality and completeness APIs, no complete match.
- Local rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `separable.point|separablePoint|separable.*completion|completion.*separable` found related
  nodal presentations, but no matching theorem or canonical point-completion interface.
- Local rg checked `namespace SeparablePoint|SeparablePoint.flat_completion_map` in Mathlib,
  WeilConjectures and Sheaf: no existing declaration with these names.

Validation: the module is compiled only through the prescribed scompile.py wrapper. The first
compile diagnosed two ideal abbreviations needing `noncomputable`; they were corrected.
No mathematical statement or hypothesis was changed. The final signature is copied verbatim
into the node's `lean.statement`; every other field of the original node is preserved.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
