## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1` states
`AlgebraicGeometry.exists_padicCharactersH1`, with its whole proof `sorry`.
It supplies three real-data helpers belonging to this comparison: the coordinate
cohomology pullback, the canonical identification of the fibre of a pulled-back cover,
and the map of fibre automorphism groups induced by pullback of covers and a path
of fibre functors. All are listed in `lean.declarations`.
The natural-language proof in the theorem docstring follows all six DAG steps.
No other theorem is introduced, no theorem is proved, and no definition uses sorry.

Hypotheses and conclusion, clause by clause:

- The globally fixed finite base field is `k₀ : Type u`, `[Field k₀]`, `[Finite k₀]`.
  The prime coefficient index is `ℓ : ℕ`, `[Fact ℓ.Prime]`, with
  `hℓ : ℓ ≠ ringChar k₀`, explicitly rendering the opening paragraph of
  `sk-d-real-setup`. No smoothness, dimension, or properness hypothesis is added.
- A model over k₀ is `p : U₀ ⟶ Spec (.of k₀)`. Geometric connectedness is
  `GeometricallyConnected p`, separatedness is `IsSeparated p`, and finite type
  is `LocallyOfFiniteType p ∧ QuasiCompact p` (Mathlib has no `FiniteType` class).
- The geometric base change is exactly `p.geometricFiber`, namely the pullback
  along `Spec (AlgebraicClosure k₀) ⟶ Spec k₀` in the upstream construction.
- The chosen geometric point is `x : Spec (.of Ω) ⟶ p.geometricFiber`, with
  `[Field Ω] [IsSepClosed Ω]`. The fundamental group is the actual `Aut (fiber x)`,
  equipped with the existing profinite topology, not an arbitrary topological group.
- Continuous additive characters are
  `Additive (Aut (fiber x) →ₜ* Multiplicative ℤ_[ℓ])`. The target's multiplicative
  tag denotes the additive group of the adic integers; the outer additive tag
  denotes pointwise addition of characters. The underlying adic topology is the
  valuation topology of `PadicInt`.
- The right side is `↥(limit (curveH1CoefficientSystem p.geometricFiber ℓ))`.
  The existing diagram has objects `Sheaf.H (U.constantZMod (ℓ ^ n)) 1`
  and coefficient reductions as transition maps, using `Functor.ofOpSequence`.
  It is defined for every scheme despite its historical name. It uses the
  `Sheaf.H` Ext model explicitly accepted by the recorded cohomology dependency;
  its equivalence with the RΓ/homology model is a stage-3 bridge, not a new definition.
- `≃+` asserts an isomorphism of abelian groups. The family `E` is chosen
  simultaneously over all models and points so that naturality is meaningful.
- The first conjunct is naturality: for every geometric-fibre morphism `f`
  and every path `τ : pullback f ⋙ fiber x ≅ fiber y`, the character `b'`
  is pointwise precomposition of `b` with the actual group homomorphism
  `padicH1FundamentalMap`. Each `limit.π` then equals the pullback of the
  corresponding coordinate. The helper is defined as whiskering with pullback
  followed by `τ.conjAut`; it is not supplied as an arbitrary map hypothesis.
  `padicH1CoordinatePullback` is `Etale.cohomologyMap` followed by `Sheaf.H.map`
  of `Scheme.upperStarConstantSheafIso`, exactly the canonical constant-coefficient map.
- In the second conjunct `s` belongs to the recorded `Scheme.FiniteEtale.weilGroup`
  for the arithmetic point `x ≫ p.geometricFiberProj`. Its degree is required
  to be `Multiplicative.ofAdd 1` using the recorded `weilGroupDeg`.
  The path for projection to the model is constructed by
  `padicH1FiberPullbackIso`, using the existing
  `Scheme.pointSmallEtaleFiberEtaleIso`. On finite-cover fibre points it is
  composition with the first pullback projection. Thus the map is canonical,
  and no extra path or action hypothesis is imposed on the Frobenius clause.
- For each geometric `g`, the last conjunct gives a geometric `h` with arithmetic
  image `s.val.1⁻¹ * image(g) * s.val.1` and `b'(g) = b(h)`. This states precisely
  inverse conjugation and also asserts the conjugate lies in the geometric group.
  The final coordinate equation is pullback along
  `p.geometricGaloisFrobenius.hom`, so this really identifies the geometric
  Frobenius action on cohomology with that character action, with no inverse switched.
  Coordinate equations describe equality of inverse-limit elements; an additional
  arbitrary endomorphism of the limit is unnecessary.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `AlgebraicGeometry.Etale.cohomology` and `rightDerivedGlobalSections`, with their
  full signatures and docstrings. The dependency record expressly permits `Sheaf.H`
  as the source library's model of the sheaf cohomology in this node.
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`:
  `constantCover`, `arithmeticFrobenius`, `constantCoverAction`, `geometricFrobenius`,
  `weilGroup`, and `weilGroupDeg` in `AlgebraicGeometry.Scheme.FiniteEtale`.
  In particular the degree convention is geometric, not arithmetic Frobenius.
- `Mathlib.NumberTheory.Padics.PadicNumbers`, `PadicIntegers`, `RingHoms`:
  `Padic`, `Padic.valuation`, `PadicInt`, `PadicInt.toZModPow`, `ker_toZModPow`,
  `zmod_cast_comp_toZModPow`, `lift`, `lift_spec`, `lift_unique`,
  `ext_of_toZModPow`, and `norm_le_pow_iff_mem_span_pow`. Their definitions and
  relevant source signatures were read. The residue leaf supplies proof ingredients.
- The landed `Sheaf.AlgebraicGeometry.Curve.H1DualTateModule`:
  `AlgebraicGeometry.curveH1CoefficientSystem`, owned by
  `lem-wf-curve-h1-dual-tate-module`. Its declaration and docstring were read.
  This existing node is added to `stmt_deps` under brief-stage2 §5's permission
  to add landed nodes. Only its general coefficient diagram is used: its theorem
  and extra curve/Jacobian hypotheses are not assumed. A transitive DAG search
  found no path from that node back to this item, hence this addition makes no cycle.
- `Scheme.FiniteEtale.fiber` and `pullback` from upstream FundamentalGroup
  modules, and `Scheme.Hom.geometricFiber`, `geometricFiberProj`,
  `geometricGaloisFrobenius` from `AlgebraicGeometry.GeometricFrobenius`.
  Their full definitions and source descriptions were read.
- `lem-wf-finite-constant-h1-pi1` has no Lean record in the current DAG.
  It remains a proof dependency; no missing notion in this statement requires
  restating that theorem. The upstream `monodromy_mapIso` is only a partial
  torsor-model statement and is not used as a replacement for that node.

Edge cases checked before and during drafting:

- Level n = 0 is included by the existing coefficient system: ZMod 1 is zero,
  so adjoining it leaves the positive-level inverse limit unchanged.
- The zero character and trivial geometric group are included; pointwise
  additive structure and the equivalence keep the zero class.
- Nonproper and nonsmooth models, and models of arbitrary dimension, are allowed.
- Every degree-one lift is quantified, including changes by geometric elements;
  commutativity of the target makes inner conjugations invisible.
- The empty geometric scheme is excluded by geometric connectedness and the
  chosen geometric point, as in the source; no unrelated nonemptiness is assumed.
- No independent smaller test universe is introduced. Schemes and their geometric
  fields have universe u, the finite-cover category and H¹ have universe u+1.
- The chapter excludes ℓ = char(k₀). The source-scope check found this ambient
  condition missing from the draft; it is now explicit in the theorem and the
  corrected node. All other primes, including ℓ = 2 when allowed, are covered.

Searches for an existing complete statement and its notions:

1. `msearch.py ... leanfinder` with query
   "Continuous p adic additive characters of etale fundamental group are the inverse
   limit of first etale cohomology with ZMod prime power constant coefficients":
   eight hits, including `PadicInt.continuousAddCharEquiv_symm_apply`, cyclotomic
   character statements and inverse-limit Galois equivalences. None has étale H¹
   as target. The additive-character result has the adic integers as source.
2. `msearch.py ... loogle 'PadicInt, ContinuousMonoidHom'`: zero hits.
3. `msearch.py ... grep 'continuousMonoidHomEquiv|H1IsoOfIsTrivial|toZModPow'
   NumberTheory/Padics`: five residue-map hits in Mathlib RingHoms, ingredients only.
4. `msearch.py ... leansearch` with query
   "inverse system of first etale cohomology with integer modulo prime power
   coefficients": eight hits, on `InverseSystem` and algebraic group cohomology;
   none is the claimed étale comparison.
5. `rg` in upstream WeilConjectures for the item id and continuous characters found
   `WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms`:
   `PadicInt.continuousMonoidHomEquiv` and its `_comp` theorem. Full definitions
   were read: these give only compatible finite continuous characters, not
   cohomology, not an additive equivalence, and not the scheme Frobenius comparison.
   They are imported as reusable ingredients, not rebound as the complete item.
6. Upstream `FundamentalGroup/Frobenius.lean` and RealSheaves/FundamentalGroup.lean
   contain partial blueprint tags and torsor/curve uses, not the full statement.
7. `rg` in `lean/Sheaf` found `curveH1CoefficientSystem` in H1DualTateModule.
   It is reused verbatim. `tools/blueprint_refs.py search 'coefficient system'`
   returned six nodes; among them the same existing dual-Tate node owns this helper.
   `rg` in DAG confirmed its recorded declaration. No duplicate system is introduced.
8. Exact-name searches for the new declarations across Mathlib, upstream,
   and `lean/Sheaf` found no existing declaration of those names.

No STATEMENT-DISPUTED issue, new node or dependency repair was needed.
The node gains the source-scope clarification documented below and the permitted
additional landed statement dependency. Its proof and proof_deps are unchanged.
All writes are confined to this item's sandbox, with compilation and delivery through
prescribed wrappers; no direct repository mutation or global build was run.

## Second reading by Q03

Author's second pass, not an independent review: the dispatcher explicitly prohibited
starting another agent; the maintainer performs the independent delivery review.
I reopened the DAG statement and module and checked every hypothesis and conclusion
against the correspondence above. Corrected the initial nonexistent `FiniteType`
identifier to `LocallyOfFiniteType ∧ QuasiCompact`; retained both Frobenius clauses,
including the degree-one constraint and the exact s⁻¹ g s direction. Reused the
already-landed coefficient system after finding it, and checked its source had no
curve-specific binder. Strengthened the explicit spelling of the action formula
from an implication to the existence of the conjugated geometric element, so its
pointwise meaning cannot be vacuous. The theorem has a single sorry, and the three
helpers have actual categorical construction data. A final pass removed the auxiliary
path hypothesis from the Frobenius clause by explicitly constructing the canonical
fibre path using `Scheme.pointSmallEtaleFiberEtaleIso`. Long lines reported by the
first successful elaboration were wrapped without changing their meaning.


## Statement corrected

Old statement, verbatim:

```tex
Let $U_0/k_0$ be geometrically connected and separated of finite type,
put $U=U_0\times_{k_0}\overline{k}_0$, and choose a geometric point
$\bar u\to U$. Put $A_n=\mathbf Z/\ell^n\mathbf Z$. There is a
natural Frobenius-equivariant isomorphism

$$
\operatorname{Hom}_{\mathrm{cont}}(\pi_1(U,\bar u),\mathbf Z_\ell)
\xrightarrow{\sim}
\varprojlim_n H^1_{\mathrm{\acute et}}(U,A_n).
\tag{3.2}
$$

Under the Weil-group action determined by a
degree-one lift $s$, Frobenius on the left is

$$
f\longmapsto\bigl[g\longmapsto f(s^{-1}gs)\bigr].
$$

The cohomology and Weil-group conventions are those of
[def-weil-pbc-etale-cohomology], [def-wf-weil-group].
The $\ell$-adic integers carry the valuation topology of [def-weil-l-adic-numbers].
```

The source chapter setup, main-20261015/sec-purity-real-sheaves/
sk-d-real-setup/_section.md, opening paragraph, fixes the finite base field
k₀ = F_q, q = p^a, and a prime ℓ ≠ p. The local node used this ambient notation
without explicitly carrying the restriction on ℓ. The corrected statement prepends
these assumptions, and the Lean theorem binds `hℓ : ℓ ≠ ringChar k₀`. This keeps
the exact source scope rather than stating the valid but stronger characteristic-p
generalization. The local isomorphism and Frobenius formula are unchanged.

Every citer found by the required search was read and audited (only membership
in stmt_deps or proof_deps counts):

- `thm-wf-rank-one-finite-geometric-image-curve`: holds true. Its statement assumes
  ℓ ∤ q, so the added explicit source convention is already available. The proof
  still applies the isomorphism to scaled integral coordinate characters and uses
  exactly the same Frobenius-equivariance clause. This citer is not edited.

The added statement dependency `lem-wf-curve-h1-dual-tate-module` only identifies
the existing general coefficient-system helper used in the signature; the
source-scope clarification requires no proof change. `old_stmt_deps` records
the complete original list; `proof` and `proof_deps` do not change.

## Maintainer review fix (cc review service, 2026-10-18)

Independent maintainer review of delivery 886bb956686e. The statement, the source-scope
correction (ℓ ≠ char k₀ from the opening paragraph of sk-d-real-setup) and its citer audit are
accepted unchanged. Two one-definition-per-notion points (H4) are corrected here:

- The helper `padicH1FiberPullbackIso` duplicated the existing
  `AlgebraicGeometry.Scheme.FiniteEtale.pullbackFiberIso`
  (`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction`), the same path
  `pullback f ⋙ fiber s ≅ fiber (s ≫ f)` given by the first projection on fibre points. The
  helper is removed; the Frobenius clause now uses `pullbackFiberIso p.geometricFiberProj x`,
  and the import of `FundamentalGroup.Functoriality` is replaced by `FundamentalGroup.Restriction`
  (which re-exports it). No hypothesis or clause changes.
- `padicH1FundamentalMap` is kept. It is the map
  `Scheme.FiniteEtale.fundamentalGroupMap τ (Aut (fiber x)) (Aut (fiber y))` (same components
  τ ∘ g ∘ τ⁻¹ on pulled-back covers), but that declaration needs a `ConnectedSpace` instance on
  the target scheme, which the theorem only has as explicit `GeometricallyConnected` proofs; its
  docstring now says so.
- The worker's search missed the upstream `AlgebraicGeometry.Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv`
  and `continuousMonoidHomPadicEquiv_comp`
  (`WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters`, tagged with this item
  in blueprint main-20261017). They do not state the node: a plain `Equiv` (no additivity) into the
  subtype `sheafHOneLimit` for a connected scheme, Frobenius equivariance only for an abstract
  transport `σ` given as a hypothesis (not the Weil-group formula `g ↦ s⁻¹ g s` for a degree-one
  lift), and no naturality for pointed morphisms. Hence the module stays a new statement; it reuses
  the landed `curveH1CoefficientSystem` for the limit.
