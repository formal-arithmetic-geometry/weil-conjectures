## Worker report

Existing declaration: `AlgebraicGeometry.Etale.kunnethMap_eq` in
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`.
Its source docstring explicitly identifies blueprint `lem-kun-kunneth-via-0f1n`.
Read the current published module with `scompile.py --source`; the older local
slopmaster2 checkout does not contain this module. No Lean module is delivered.

The saved packet had two concrete faults: its conclusion equated
`kunnethGlobalSectionsMap` with itself, and its signature omitted finite type of
X and Y. Its report claimed a projection composite that the file did not contain.
The existing published theorem supplies the actual identity, so the packet now
records it instead of introducing a duplicate statement. The DAG's mathematical
statement and all its other fields are unchanged. The old dispute concerned an
absent interface; the published source supplies that interface and resolves it.

Hypothesis-by-hypothesis specialization of the existing declaration:

- Take `S := Spec (.of k)` for the given field `k : Type u` with `[Field k]`
  and `[IsSepClosed k]` (`def-kun-separably-closed`, Mathlib `IsSepClosed`).
  The identity holds over any base; the separably closed assumption gives the
  canonical interpretation in module-valued global sections used by the node.
- Take `A := ModuleCat.{u+1} (ULift.{u+1} (ZMod n))` for the given integer
  `n : ℕ`, `0 < n`, and `IsUnit (n : k)`. This is the same coefficient encoding
  as the recorded Kunneth and 0F1N dependencies. `ULift.ringEquiv` identifies the
  coefficient ring with Z/n. No finite, torsion, invertibility or nonzero-ring
  assumption is required to establish this map identity; those source hypotheses
  ensure the projection and 0F1N maps are isomorphisms in its application.
- Use the given finite-type X and Y with structure maps `f : X ⟶ S`,
  `g : Y ⟶ S`. Finite type is `[LocallyOfFiniteType f] [QuasiCompact f]`
  and the analogous instances for g. The existing identity applies to every f,g,
  hence in particular to every scheme satisfying these hypotheses. It places no
  separatedness, properness, smoothness, or boundedness restriction on them.
- Take `W := pullback f g`, `p := pullback.fst f g`,
  `q := pullback.snd f g`, `c := p ≫ f`, `hp := rfl`, and
  `hq := pullback.condition.symm`. This is precisely the product square.
- The displayed binders `E : DerivedCategory (Sheaf X.smallEtaleTopology A)`
  and `K : DerivedCategory (Sheaf Y.smallEtaleTopology A)` range over the
  arbitrary unbounded derived objects of the node, with no cohomological bounds.

Clause-by-clause correspondence of the conclusion:

1. The left side `kunnethMap A p q f g c hp hq E K` is the canonical counit
   adjunct in `def-kun-kunneth-map`. Its module-valued global sections is exactly
   `kunnethGlobalSectionsMap`, the recorded dependency declaration: inspection of
   that definition shows inverse Leray on each input, the canonical tensor
   comparison at Spec k, global sections of this very `kunnethMap`, and Leray
   for c. Thus it is the node's κ, rather than an arbitrary external product.
2. The first factor on the right is
   `((rightDerivedLowerStarProjectionMap A f).app E).app
     ((lowerStar A g).rightDerivedFunctor.obj K)`.
   It is the counit mate of the derived inverse-image tensor comparison, with
   source `Rf_*E ⊗ Rg_*K` and target `Rf_*(E ⊗ f⁻¹Rg_*K)`.
   Under the canonical constant-sheaf/evaluation equivalence at the separably
   closed point, `Rg_*K` is RΓ(Y,K), and its inverse image is the constant
   complex on X. Taking global sections and Leray for f gives exactly the first
   displayed projection-formula arrow of the node (0F12). This identifies the
   arrow itself, including its counit normalization, not just its endpoints.
3. The second factor is `Rf_*` of
   `tensorBaseChangeMap A p q f g (hp.trans hq.symm) E K`.
   Its type is `E ⊗ f⁻¹Rg_*K ⟶ Rp_*(p⁻¹E ⊗ q⁻¹K)`.
   This is precisely φ for the diagram in the node, the canonical map used by
   the recorded 0F1N theorem. Applying global sections gives RΓ(X,φ).
   The identity leg in that diagram is absorbed by the canonical identity
   inverse-image comparison, with no arbitrary isomorphism substituted.
4. The final factor `rightDerivedLowerStarCompIsoOfComp A p f c hp` is the
   canonical composition isomorphism `Rp_* ⋙ Rf_* ≅ Rc_*`, defined by
   conjugating the canonical inverse-image composition through the derived
   adjunctions. Under global sections and the canonical Leray identifications,
   it gives exactly the last identification RΓ(X,Rp_*B) ≅ RΓ(W,B).
   Its normalization agrees with composite counits, as also shown by the
   immediately preceding published lemma
   `map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit`.

Dependency declarations read:

- `def-kun-kunneth-map`: `Sheaf.AlgebraicGeometry.KunnethGlobalSections`,
  `AlgebraicGeometry.Etale.kunnethGlobalSectionsMap` and
  `pointGlobalSectionsTensorIso`; the public upstream `kunnethMap` is the
  general-base definition transported by these real canonical comparisons.
- `lem-kun-0f1n`: upstream Ordinary, `isIso_tensorBaseChangeMap`, whose full
  signature and the defining `tensorBaseChangeMap` were read in the published
  source. Specialization of its identity first leg gives the map above.
- `lem-kun-leray-unbdd`: upstream Derived.GlobalSections,
  `rightDerivedLowerStarCompRightDerivedGlobalSectionsIso`, constructed from
  `lowerStarCompGlobalSectionsIso` and the K-injective derived composition.
- `def-kun-separably-closed`: Mathlib.FieldTheory.IsSepClosed,
  `IsSepClosed` and `IsSepClosure`; both signatures and docstrings were read.

Edge cases checked: n=1 gives the zero coefficient ring and zero derived category;
empty X or Y still admits the product projections and all the canonical maps;
zero E or K, X=Y=Spec k, arbitrary shifts and unbounded complexes are all covered.
No nonemptiness or nontrivial coefficient assumption occurs. Non-separated finite-type
schemes are included, since the existing map identity assumes no scheme properties.
The coefficient and site universes are those of the recorded dependency interfaces.

Searches (2026-10-17):

- `msearch.py leanfinder`, query “The etale Kunneth map equals the projection
  formula map followed by tensor base change and the pushforward composition
  isomorphism”: eight hits about Kaehler differentials and scheme pullback
  carriers; none is this derived map identity.
- `msearch.py loogle`, query `"kunneth"`: zero hits.
- `msearch.py grep`, query `kunneth|projectionFormula|projection_formula`:
  zero Mathlib hits.
- `rg -n 'kunnethMap_eq|lem-kun-kunneth-via-0f1n|tensorBaseChangeMap'` over
  the named local WeilConjectures and lean/Sheaf source directories: no hits.
  The local Ordinary path is missing; this is a stale-source issue, resolved by
  the prescribed source reader rather than by duplicating the declaration.
- `scompile.py --source
  WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary`: exact existing
  theorem `kunnethMap_eq`, explicitly labelled with this blueprint node. Read
  its complete section parameters, statement, docstring, and the definitions
  of all three factors on its right side. The equality has no extra premises.

Self-check: this is an existing general-base identity specialized to the exact
source situation and read through the same canonical point/Leray identifications
as the recorded Kunneth definition. It asserts equality of the specified maps,
not equality with itself, Nonempty of an isomorphism, or just invertibility.
No statement correction or dependency repair is needed.

Validation: compiled `scratchpad/ExistingCheck.lean` through
`scompile.py Q54 lem-kun-kunneth-via-0f1n scratchpad/ExistingCheck.lean`.
It imports the published module and checks the full specialization of
`kunnethMap_eq` at `ModuleCat (ULift (ZMod n))`, the product projections,
`hp := rfl`, `hq := pullback.condition.symm`, and the arbitrary E,K.
Both wrapper checks succeeded without errors or warnings (3.4 s and 3.5 s).
The printed type contains all three specified factors of the composite.
The scratch check introduces no declaration and is not part of the delivery.

## Earlier second reading (a previous round; superseded)

Pending the separate independent second reader requested in the dispatch brief.
The preceding self-check is the worker's check, not an independent review.

## Second reading by Q54

I read the node, its blueprint source, the dependency records, and the complete
published declaration before accepting the existing record. The item-by-item
translation is as follows.

- The node's objects are a separably closed field `k`, an integer `n ≥ 1`
  invertible in `k`, finite-type `k`-schemes `X,Y`, arbitrary unbounded
  `E : D(X_ét, ℤ/nℤ)` and `K : D(Y_ét, ℤ/nℤ)`, and the product square. In the
  published declaration these are `A`, schemes `S,X,Y,W`, maps
  `p q f g c`, equalities `hp hq`, and arbitrary `E,K`; the specialization is
  `A := ModuleCat (ULift (ZMod n))`, `S := Spec (.of k)`, `W := pullback f g`,
  `p := pullback.fst f g`, `q := pullback.snd f g`, `c := p ≫ f`,
  `hp := rfl`, and `hq := pullback.condition.symm`. The recorded
  `LocallyOfFiniteType` and `QuasiCompact` instances render finite type for
  both structure maps. Verdict: every object and hypothesis is present; the
  published theorem is more general and adds no hypothesis.
- The node's first conclusion clause is the Künneth map from
  `def-kun-kunneth-map`. It is rendered by
  `AlgebraicGeometry.Etale.kunnethMap A p q f g c hp hq E K`; its canonical
  global-sections transport is the recorded
  `AlgebraicGeometry.Etale.kunnethGlobalSectionsMap`. Verdict: same map and
  same adjunction normalization.
- The first composite factor is the projection-formula map of `lem-kun-0f12`.
  It is rendered by
  `((rightDerivedLowerStarProjectionMap A f).app E).app
  (R((g)_*[A]).obj K)`. Verdict: this is the canonical counit mate, not an
  arbitrary comparison.
- The second factor is `R f_*` applied to the `lem-kun-0f1n` map for the
  displayed product diagram. It is rendered by
  `R((f)_*[A]).map (tensorBaseChangeMap A p q f g
  (hp.trans hq.symm) E K)`. Verdict: the maps and diagram orientations agree;
  `hp.trans hq.symm` is exactly `p ≫ f = q ≫ g`.
- The final factor is the Leray/composition identification from
  `lem-kun-leray-unbdd`, rendered by
  `(rightDerivedLowerStarCompIsoOfComp A p f c hp).hom.app _`. Verdict: the
  canonical composition isomorphism has the required direction and
  normalization.

The source check was made at the blueprint node and Stacks Tags 0F1N and 0F1P.
Tag 0F1N assumes only a field, `n ≥ 1` invertible in it, finite type, and
arbitrary unbounded derived objects; Tag 0F1P supplies the separably closed
Künneth setting. No properness, separatedness, boundedness, nonzero scheme, or
nonzero coefficient assumption is hidden in the Lean specialization.

Edge cases checked independently: `n = 1` (the zero coefficient ring), empty
`X` or `Y`, zero `E` or `K`, `X = Y = Spec k`, arbitrary shifts and unbounded
complexes, and non-separated finite-type schemes. The universe is shared by
`k`, schemes, sites, and the lifted coefficient module category exactly as in
the dependency declarations; no extra universe equality is imposed.

I repeated the existing-definition searches with `msearch.py` (LeanFinder and
Loogle queries for Künneth/projection maps), grep over Mathlib and both named
WeilConjectures/lean/Sheaf trees, and `scompile.py --source` for the published
module. Only the published declaration
`AlgebraicGeometry.Etale.kunnethMap_eq` matches, and its docstring explicitly
names `(blueprint: lem-kun-kunneth-via-0f1n)`. The dependency declarations were
opened and match their node signatures. The local source tree's missing module
is a stale-checkout issue handled by the prescribed source reader.

No mismatch remains in the delivered node. The earlier packet's self-equality
conclusion and omitted finite-type hypotheses were corrected before this
reading; I verified the corrected node and did not introduce another statement
change. The existing Lean record therefore needs no module or dependency
repair. The independent specialization check in `scratchpad/ExistingCheck.lean`
compiled twice through `scompile.py` with no errors or warnings.
