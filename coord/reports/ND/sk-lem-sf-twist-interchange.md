## Worker report

This delivery records an existing upstream statement family and creates no Lean module.
The source is the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-lem-sf-twist-interchange/_section.md`.
Its statement is identical to the item's statement. There is no repair note for this item.
Only the item's `lean` field changes; its statement and dependencies stay unchanged.

The primary declaration is
`AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_derivedHom_tensor` in
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.Dual`.
The recorded module is its defining module `Perfect.Dual`. The separately read
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist` publicly imports it and
contains an explicit concrete shifted specialization; that additional theorem is
documented below rather than listed as a declaration of `Perfect.Dual`.
The primary signature in `lean.statement` is copied verbatim from `Perfect.Dual` up to `:=`.
Both modules were read in the local upstream/side sources and confirmed using
`scompile.py --source` against the current server sources.

Hypotheses and clauses:

- `X` is `Scheme.{u}`. The ambient objects `K`, `T`, and `M` are in
  `_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)`. Taking the coefficient category
  `A = ModuleCat.{u + 1} Λ` gives the coefficient derived category `D(X, Λ)` used here.
  The enclosing coefficient-category instances provide its derived tensor and closed
  structure; these are the existing library implementation, not replacement operations.
- Perfectness is exactly `(hK : IsDualizable K)`, as the node explicitly defines it.
  There is no boundedness or constructibility hypothesis on `K` or `M` in this node.
- Invertibility of the arbitrary derived object `T` is exactly
  `(_hT : IsInvertible T)`. This is categorical tensor invertibility, not an ordinary
  invertible sheaf hypothesis. `M` is an unrestricted object of the same derived category.
- `RHom_X(K, -)` is `(RHom(X)[A].obj (op K)).obj`; `⊗` is the existing derived tensor
  monoidal structure. The primary conclusion is precisely
  `Nonempty ((RHom(X)[A].obj (op K)).obj (M ⊗ T) ≅
    (RHom(X)[A].obj (op K)).obj M ⊗ T)`.
- The node specifies the canonical map, so the primary existential isomorphism is not
  recorded alone. `derivedHomTensorMap K M T` is defined as
  `MonoidalClosed.ihomTensorToIhom K M T`, the tensor–Hom transpose of evaluation tensored
  with `1_T` (with the associator). `isIso_derivedHomTensorMap K hT M` proves this map is
  invertible. The explicitly constructed `derivedHomTensorIso K hT M` is
  `(asIso (derivedHomTensorMap K M T)).symm`, so its forward arrow has exactly the
  direction in the node. These declarations establish canonicality, rather than only
  the existence of an unspecified isomorphism. Their availability for arbitrary `K`
  includes the node's perfect `K`; the node itself is not changed or generalized.
- The Tate-twist example is the existing `tateObject Λ X m`, with `m : ℤ`.
  `isInvertible_tateObject` supplies tensor invertibility, and
  `DerivedCategory.isInvertible_shift` supplies invertibility after every `n : ℤ` shift.
  The concrete etale notation presupposes the library's existing `HasTateTwist Λ` datum.
  The concrete shifted theorem below also retains `[HasInvertibleExponent Λ X]`; this
  belongs to that torsion-coefficient specialization and is not a hypothesis on the
  arbitrary-invertible-object assertion. The general final clause is already the
  canonical `derivedHomIsoCoefficientDualTensor` applied to the invertible shifted
  twist, followed by the derived tensor shift isomorphism. Thus that clause uses only
  invertibility of the twist, including when using other coefficient-stage models; the
  more specialized concrete theorem is not used to restrict the node to torsion rings.
- At the concrete torsion-coefficient stage, the entire last clause is also supplied by
  `AlgebraicGeometry.Etale.nonempty_iso_derivedHom_tateObject_shift`:
  `Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((tateObject Λ X m)⟦n⟧) ≅
    ((tateTwist Λ X m).obj
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)))⟦n⟧)`.
  The coefficient dual is the existing `RHom(K, 𝟙)` definition; `tateTwist` tensors on
  the right with `tateObject`. This is `RHom(K, Λ_X(m)[n]) ≅ K^∨(m)[n]`.
  It is constructed from the canonical `derivedHomIsoCoefficientDualTensor`, followed
  by the derived tensor's shift isomorphism.

There are no statement-dependency nodes (`stmt_deps` is empty), hence no dependency
records or interfaces to repair. The declarations above use the existing upstream
`derivedHom`, `derivedTensor`, `coefficientDual`, `tateObject`, and `tateTwist` definitions.
No copies, helper definitions, new nodes, postponed theorems, or proofs are introduced.
The generic categorical proof already in upstream implements the node's proof:
right tensoring by an invertible object is an equivalence; tensor–Hom adjunctions
identify the two represented functors, and evaluation identifies that isomorphism with
the canonical map. Taking the coefficient unit and then a shifted Tate object gives
its final clause. No generator argument is required.

Edge cases checked by reading the signatures and constructions: `K = 0` and `M = 0`
are permitted; `T` may be the unit; the empty scheme is not excluded; the generic
statement has no characteristic restriction. Both twist and shift indices range over
all integers, including zero and negative values. No separate bound on `M` or `n` is
introduced. In a nonzero category a noninvertible zero object is correctly excluded by
`IsInvertible T`; the trivial category is covered as well. The primary coefficient
universe `u'` and scheme universe `u` are explicitly bound upstream; module coefficients
use the established `ModuleCat.{u + 1}` size convention.

Searches for existing statements (all through `msearch.py ND sk-lem-sf-twist-interchange`
when a search-service tool is named):

- LeanFinder: `internal Hom tensor with invertible object canonical map is an isomorphism`.
  Eight hits concerned internal Hom adjunctions, unit isomorphisms, and rigid tensor
  adjunctions; none supplied this derived statement.
- Loogle: `CategoryTheory.MonoidalClosed.ihomTensorToIhom, CategoryTheory.IsInvertible`.
  No hits; the service did not know the upstream-only comparison name.
- Mathlib grep: `ihomTensorToIhom|isIso_ihomTensorToIhom` in `CategoryTheory`.
  No hits. The actual categorical comparison is in the upstream extension
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`.
- LeanSearch: `internal hom tensor invertible object`. Eight hits included `ihom`,
  `internalHom`, their adjunctions, and ordinary invertible-module tensor facts;
  no derived comparison theorem.
- Upstream text search: `rg -n 'nonempty_iso_derivedHom_tensor|isIso_derivedHomTensorMap'`
  and the prescribed blueprint-id search in `WeilConjectures`. These found
  `Perfect/Dual.lean`, its categorical core, and `Perfect/TateTwist.lean`.
  The full signatures, docstrings, and canonical constructions were read.
- Side-project search in `lean/Sheaf`:
  `derivedHomTensor|derivedHom_tateObject_shift|iso_derivedHom_tensor` found no competing
  statement. The side `lean/WeilConjectures` contains the same usable upstream family.
- `dag/lean_names_upstream.json` was searched for the comparison names and the notions
  `IsInvertible` and `IsDualizable`; the item's `lean_audit.slopmaster2` independently
  identifies the primary theorem in `Perfect.Dual` as an existing closed declaration.

No statement dispute or node fault was found. The existing declaration family is
recorded together so that neither canonicality nor the shifted final clause is lost.

Validation: a separate `scompile.py` signature probe compiled cleanly against both the
sandbox overlay and published library (5.6 s and 4.9 s). Its elaborated types confirm
that the primary theorem retains `IsDualizable K` and `IsInvertible T`, the canonical
comparison theorem needs only `IsInvertible T`, and the concrete Tate specialization
quantifies over all `m n : ℤ`. The required dry run additionally performs real server
`#check` compilation of every recorded declaration through the recorded defining module and runs the current server
preflight. The first dry run compiled cleanly but preflight required the primary
declaration's defining module rather than its public re-exporting module; that record
was repaired to `Perfect.Dual`, and the concrete Tate specialization was removed from
`lean.declarations` (its full statement remains documented above).

The five recorded declarations all belong to `Perfect.Dual`. The final formula is
already its `derivedHomIsoCoefficientDualTensor K hT` for
`T = Λ_X(m)[n]`: shift preserves tensor invertibility, and the tensor shift isomorphism
identifies `K^∨ ⊗ Λ_X(m)[n]` with `(K^∨ ⊗ Λ_X(m))[n] = K^∨(m)[n]`. The separate concrete
theorem confirms the exact formula; its extra torsion-coefficient class does not
restrict the generic invertible-object declaration family recorded for this item.


## Second reading by ND

I independently opened the sandbox node, its blueprint source at order 2505, the
surrounding `sec-six-functors/_section.md`, and the full existing modules `Perfect.Dual`,
`Perfect.TateTwist`, `Derived.Hom`, `Derived.Tensor`, `Perfect.Invertible`, and the categorical
`Mathlib.CategoryTheory.Monoidal.Rigid.Basic` extension. The source is the blueprint, not a
Stacks tag. I also fetched `Perfect.Dual` with `scompile.py --source`; its current server
signature agrees with the recorded signature. There is no repair note, statement correction,
new node, dependency module, or delivered Lean module. The item's `stmt_deps` is empty.

Object/hypothesis/conclusion checklist, in source order:

1. Ambient `X` and coefficients: `X : Scheme.{u}` and
   `DerivedCategory (Sheaf X.smallEtaleTopology A)`, specialized to
   `A = ModuleCat.{u + 1} Λ`, implement the unbounded coefficient derived category.
   The general signature binds `A : Type u'` independently of `u`, with hom universe `u+1`.
   Its Abelian/Grothendieck, symmetric monoidal, closed, and functorial-flat-resolution
   instances are the existing tensor/Hom infrastructure; for module coefficients they
   synthesize from `[CommRing Λ]`, without extra finiteness or Noetherian assumptions.
   The chapter discusses finite-type schemes over the algebraic closure of a finite field
   and coefficient stages. This existing categorical identity works on arbitrary schemes
   and specializes to those contextual schemes; it does not impose a new geometric
   restriction. Verdict: the required ambient derived operations are supplied.
2. `K` is perfect, expressly meaning tensor-dualizable in this node:
   `{K : DerivedCategory (Sheaf X.smallEtaleTopology A)}` and `(hK : IsDualizable K)`.
   I read `IsDualizable`: it is `Nonempty (HasRightDual K)`; symmetry identifies left/right
   dualizability here. No substitution of constructibility or boundedness occurs.
   Verdict: exact hypothesis.
3. `T` is an arbitrary tensor-invertible complex in that same category:
   `{T : ...}` and `(_hT : IsInvertible T)`. I read `IsInvertible`: it demands an object
   with both tensor products isomorphic to the unit. It is not invertibility of an
   underlying ordinary sheaf. Verdict: exact object and hypothesis.
4. `M` is any object of the same derived category: `(M : ... )`, after the two
   hypotheses. There is no constructibility, finite Tor-amplitude, or boundedness binder.
   Verdict: exact quantification, including arbitrary unbounded `M`.
5. The displayed source and target are, respectively,
   `(RHom(X)[A].obj (op K)).obj (M ⊗ T)` and
   `(RHom(X)[A].obj (op K)).obj M ⊗ T`. `derivedHom` is the internal Hom right adjoint
   of the existing derived tensor; these are the correct functors and tensor order.
   The primary theorem gives `Nonempty` of the isomorphism with exactly these endpoints.
   I mechanically compared `lean.statement` with the defining source up to `:=`:
   verbatim equality holds. Verdict: exact displayed objects and direction.
6. Canonicality is not a consequence of an arbitrary `Nonempty` isomorphism, so I checked
   the other four recorded declarations rather than accepting the primary name alone.
   `derivedHomTensorMap K M T` is `MonoidalClosed.ihomTensorToIhom K M T`, whose actual
   data is `curry ((α_ _ _ _).inv ≫ (ihom.ev K).app M ▷ T)`. This is precisely the
   evaluation transpose called `c_{M,T}` in the node's proof (using left evaluation,
   equivalent to the source's symmetric ordering). `isIso_derivedHomTensorMap K hT M`
   asserts its invertibility. `derivedHomTensorIso K hT M` is literally
   `(asIso (derivedHomTensorMap K M T)).symm`. Its forward arrow is the node's canonical
   arrow. These helpers work without dualizability, but are applied here with the
   primary theorem's `hK`; the node and its hypotheses are retained. Verdict: canonical
   map and its isomorphism property are present, not merely unspecified existence.
7. For all integers `m,n`, the last clause follows by setting the invertible object to
   `Λ_X(m)[n]` in the recorded `derivedHomIsoCoefficientDualTensor` and using the right
   tensor shift isomorphism. I read `coefficientDual`: it is `RHom(-, 𝟙)`; I read
   `tateTwist`: it tensors on the right with `tateObject`. I read `isInvertible_shift`,
   which uses shifts `n` and `-n` on a tensor inverse. Thus the result is exactly
   `RHom(K, Λ_X(m)[n]) ≅ (K^∨(m))[n]`. The separate existing
   `nonempty_iso_derivedHom_tateObject_shift` spells out this entire formula and its
   construction. Its `[HasTateTwist Λ] [HasInvertibleExponent Λ X]` belong to that
   concrete torsion-coefficient model; they are not extra assumptions on the recorded
   generic interchange or on its application to any supplied invertible twist.
   Verdict: the final clause is the unit/shift specialization of the recorded family;
   no torsion restriction has been inserted into the item's arbitrary-`T` statement.

Proof and definition audit: the categorical invertibility proof realizes the node's
argument by the tensor-right equivalence from the two-sided inverse, tensor/Hom
adjunction, and Yoneda. The evaluation transpose identifies its canonical comparison.
The alternate dualizable proof is the coefficient-dual identification twice and the
associator, exactly as described in the node. The unit and shift give the last step.
All data just inspected are actual constructions, not `sorry` or arbitrary object choices.
This existing-only delivery introduces no proof, axiom, definition, local notation, or
instance. H8's requirements on newly written statement modules are vacuous; the existing
module's documentation identifies the blueprint, and the full stepwise proof is also
preserved in the node and explained here.

Edge cases: no index family occurs; the empty scheme is allowed; `K=0`, `M=0`, and the
unit twist are allowed. The zero twist is allowed exactly when tensor-invertible (as in
a trivial category), which is what the source says. All integers `m,n`, especially zero
and negative values, occur. No characteristic or positivity condition enters the generic
identity. The small etale site and `ModuleCat.{u+1}` convention retain the scheme universe;
there is no imposed equality between independent coefficient-object and scheme universes.

Independent searches, with queries different from the first reader's:

- LeanFinder via `msearch.py`: `tensoring internal hom by a tensor invertible object
  commutes with internal hom`; eight hits, including `tensorRightHomEquiv_tensor`,
  `tensorLeftHomEquiv_tensor`, and the corresponding Hom equivalences, but no competing
  derived interchange declaration.
- Loogle via `msearch.py`: `CategoryTheory.ihom`; twelve hits, supplying the ordinary
  internal Hom, adjunction, evaluation/currying, and unit comparison, not this derived
  invertible-twist assertion.
- LeanSearch via `msearch.py`: `closed monoidal category internal Hom commutes with
  tensoring by invertible object`; eight hits, mainly `MonoidalClosed.internalHom`,
  `ihom`, and closed subcategory infrastructure; no additional exact match.
- `rg` for `ihomTensor|tensor.*ihom|ihom.*tensor|derivedHomTensorIso|iso_derivedHom_tensor`
  in Mathlib's monoidal category directory, upstream `Perfect`, and project `lean/Sheaf`
  found the existing `Perfect.Dual` family and unrelated sheaf/Picard comparisons.
  I followed the upstream imports to the actual categorical comparison and read it.
  A separate `rg` over `dag/lean_names_upstream.json` and the upstream rigid extension
  checked the names and the blueprint-id annotation. No private replacement is needed.

Mismatches and changes: none in the node or declaration binding. The primary theorem
alone would not express canonicality, but the worker already recorded its defining map,
its invertibility theorem, its canonical inverse and its coefficient-dual specialization;
I verified all five. I leave the correct record unchanged and add this independent audit.
The scratch signature probe was expanded to check all five declarations, the shift
lemma, the concrete shifted formula, and specialization to arbitrary commutative module
coefficients, so instance synthesis is checked rather than inferred from names.
