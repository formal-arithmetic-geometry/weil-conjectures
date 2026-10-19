# Worker report: def-trf-frobenius-operators

## Files written

- `dag/nodes/sec-six-functors/def-trf-frobenius-operators.json`: definition, split by naming the existing constructions and theorems that its two operators use; no Mathlib match.
- `citations.json`: `[]`, because this definition has no proof steps and no proof dependencies.

There are **0 new nodes** and **0 Mathlib leaves**. `searches.jsonl` is the search command's evidence log; `prepare.py` is sandbox-only preparation material.

## Attachments

None. I searched the project Lean under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the node tag, Frobenius operators, local/stalk Frobenius and iterated Weil maps, and checked `dag/lean_names_upstream.json`. `AlgebraicGeometry.Etale.frobeniusOperator` in `WeilConjectures/SixFunctors/Etale/Derived/WeilFrobenius.lean:113` defines the operator on `Hom(1,M)` for an arbitrary Weil datum. Its tag does not supply the finite-coefficient compact-support construction and local operators in the item. `AlgebraicGeometry.ProEtale.WeilComplex.stalkFrobenius` in `WeilConjectures/SixFunctors/ProEtale/TraceFormula/Frobenius.lean:295` gives a local operator for a chosen base-linear endomorphism and a supplied fixed-point equality; it does not include the geometric-Galois/scheme-Frobenius comparison or the global coefficient-complex operator. The same file's `coeffIterate_one` and `stalkFrobenius_eq_pow` are sorried. I therefore make no exact attachment claim and do not count these project declarations as finished proofs of this item.

## WANTED

None. The current blueprint, Deligne Weil II, and the Stacks source needed to check the comparison route are present locally.

## Faults and changes

I followed `blueprint_update.statement` and read the complete current node at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-rf-shriek-preservation/def-trf-frobenius-operators.md`, both clauses and the following equivalent-description paragraph. The imported statement left the input category and the iterated Weil map without their definition dependencies. I added `def-trf-strict-weil-complex` and `def-trf-iterated-weil-map`.

The existing `def-weil-global-geometric-frobenius` is stated for E-Weil complexes, whereas this item is at the finite ring A. I did not apply that E-only statement to A. The pre-existing `def-weil-frobenius-cohomology-transport` explicitly covers A, and its isomorphism theorem explicitly covers A as well. I used its actual transport composite and iterated it through derived pullback-composition isomorphisms. The operator on a coefficient complex is now distinguished from its induced operator on each cohomology module. This supplies the unnamed canonical identification of clause 1 at its correct coefficient stage.

Clause 2's canonical stalk transport is now an actual formula: the fixed-point equality for the k-linear scheme Frobenius gives rho, and the specified comparison kappa gives tau. In particular, this construction does not infer a scheme-morphism equality `g_gamma^m o xbar = xbar` from a rational point. That inference would be false already for `X_0 = Spec F_q`, where `g_gamma^m = Spec(gamma^m)` on `Spec k` is nonidentity. The current blueprint supplies scheme-Frobenius fixed points together with the comparison, so it has a sound interpretation; the formula makes that interpretation explicit. This is a clarification of the source's transport, not a change of Frobenius convention. The geometric lift is the one induced by the chosen finite-field point and the fixed inclusion into k. The point fiber functor is written explicitly when the stalk is viewed in D(A).

Removed direct dependencies on the unused cohomology-sheaf definition, the direct-image definition, the E-only global definition, and universal-homeomorphism invariance. The needed compact-support functor and coefficient cohomology are already explicitly part of the cited cohomology and transport definitions. Universal-homeomorphism invariance is used upstream by the specified comparison; its equivalence assertion alone would not specify the local transport. All original pointers and blueprint/import metadata remain intact. The three downstream lemmas remain pointers and create no backward edge.

The node remains in its inherited chapter and unit. The current unit record has been updated to an f-shriek preservation theorem in `sec-six-functors-basics`; this is a recorded-in-advance definition of trace-formula notation, and has no proof route to replace. I did not modify the maintainer-owned unit binding or its realization.

## Unfinished work

No additional mathematical sublemma is needed for this one-level definition split. The cited nodes retain their own existing proof obligations. The second reader must inspect this split and perform delivery; this worker runs only the required dry run.

## Not duplicates

No new nodes. Searches of the whole DAG and `tools/blueprint_refs.py search` for `Frobenius operators`, `stalk transport`, `iterated Weil`, and `geometric Frobenius` found the existing strict-Weil, iterate, cohomology transport, and comparison interfaces used here. The E-only global operator and the constant-Qbar operator `def-tw-frobenius-action` do not state both finite-ring clauses of this item; `same_as` is therefore empty.

## Review by Q117

I opened the current blueprint definition and its imported JSON, the containing chapter and unit records, and each dependency statement used below. For the convention behind the constructions I read Deligne, *La conjecture de Weil II*, (1.1.7), (1.1.8), (1.1.10)--(1.1.14), printed pages 150--153 (PDF pages 15--18). These distinguish the geometric Galois action, its action on cohomology by transport, and the Frobenius at a finite-field-valued point. The finite-level operators in this definition use the blueprint's finite coefficient category throughout. For the upstream scheme/Galois comparison I also read Stacks Tag **0F6W**, `more-morphisms.tex`, `lemma-relative-frobenius-weakly-etale`: the relative Frobenius of a weakly etale morphism is an isomorphism. This supports the existing absolute-Frobenius-site interface and does not by itself assert the global compact-support result. No SGA route or source is used in this split.

This is a definition, so there are no numbered proof steps. I checked its two construction clauses as follows.

For clause 1, `def-trf-coefficient-conventions` supplies A, separated finite type X_0, the small pro-etale setting, and compact-support coefficient cohomology; `def-trf-strict-weil-complex` supplies the actual finite-ring pair and forgetful functor; and `def-trf-iterated-weil-map` supplies an isomorphism with source L(g^m)^*M, exactly the source needed after transport. I read `def-weil-frobenius-cohomology-transport` and checked that its compact-support arrow is defined for every N in D^b_c(X,A), with target RΓ_c(X,Lg^*N). Its statement explicitly places each pullback back in the constructible category. Thus all successive T^jM are legitimate inputs. `lem-weil-frobenius-cohomology-transport-iso`, clause 3, supplies the isomorphism of each arrow, at A rather than only E. `lem-weil-pbc-proetale-derived-pullback-composition` supplies precisely L(k o h)^* ≅ Lh^*Lk^* on the constant-coefficient ringed pro-etale sites: inverse images of the constant A-sheaf have their canonical identifications, so its ring hypotheses apply. The finite composite is therefore type-correct, and applying RΓ_c to phi^[m] returns to the starting complex. This uses no separate equality identifying an unspecified base-change map with transport. `def-weil-ordinary-compact-cohomology` defines both RΓ_c and H_c^i, including the coefficient cohomology functor. The last sentence simply applies that functor to the constructed morphism.

For clause 2, I checked the exact statement of `thm-trf-frobenius-fixed-points`: its fixed scheme is a disjoint union of Spec k indexed by X_0(F_{q^m}). I use only this clause to obtain Phi^m o xbar = xbar for the induced k-point, not its additional transversality assertion. Pullback-composition then gives rho in the displayed direction. I read `prop-trf-scheme-galois-comparison`: it supplies the specified natural isomorphism kappa^(m) from scheme-Frobenius pullback to geometric-Galois pullback, in the direction used in tau. Its coefficient hypothesis holds because A is a finite commutative ell-primary ring, annihilated by a power of ell, and ell is invertible in k. Applying the functors Lxbar^* and Fib_s to an isomorphism preserves invertibility. The final map is Lxbar^* of phi^[m], followed by the same Fib_s, so its source is exactly the target of tau and its target is the original stalk coefficient complex. I read `def-weil-finite-coefficient-point` to check that the finite-ring fiber is termwise sections on Spec k, and `def-weil-derived-pullback-tensor-hom` to check that finite coefficient pullback is the constant-coefficient inverse image, not a pullback of structure-sheaf modules. These choices agree with the item's finite-ring setting.

For B1--B9 and D1--D5, no new statement node or elementary helper was introduced, no proof or clause was moved into a new node, and the definition carries empty proof/proof_deps. I checked the dependency statements themselves rather than borrowing from their proofs. The displayed composites exhaust the data of both operators; their non-elementary identifications are the named existing theorem interfaces just checked. The only equality transport used in rho is substitution of the fixed-point equality, an elementary operation. The three forward-pointer lemmas are left outside stmt_deps to avoid circularity. All Mathlib queries were run with msearch.py and recorded from its output: the first Loogle query was invalid (unknown identifier) and was superseded by the successful quoted `Frobenius` search; it is recorded as invalid rather than evidence of absence. LeanSearch and both LeanFinder phrasings returned field/Witt-vector Frobenius or ordinary module-pullback constructions, not the operator pair. Grep located `FiniteField.frobeniusAlgEquivOfAlgebraic` at `Mathlib/FieldTheory/Finite/Basic.lean:363` and `Scheme.Modules.pullbackComp`/`pullbackCongr` at `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:241,261`; I read these definitions and checked that none supplies derived pro-etale compact support and local Weil operators. No unavailable service was reported as a negative result.

For E1--E6 I checked m=1, the zero complex, the empty X, and the point X_0=Spec F_q. At m=1 the global transport composite has one factor and the local operator is the single Weil isomorphism after rho and kappa. For the zero complex all maps are the unique zero-object maps. For empty X, compact-support cohomology is the zero object and there is no local point to choose. For a point, Phi is the identity but the semilinear g is not; the specified comparison gives the required stalk identification without a false fixed-point equality for g. No connectedness, smoothness, properness, or extension to rational coefficients has been added. In particular, the local construction uses no smooth-locus or transversality hypothesis. I corrected the missing dependency names, the finite/E coefficient mismatch, the implicit point-fiber identification, and the type ambiguity between a complex endomorphism and its cohomology maps during this review.

## Second reading by Q117

I independently read `coord/delivery-errors.md` B--E, `GOAL.md`,
`coord/dag-sync.md`, the item's chapter/unit records, the sandbox JSON, the
current `main-20261015` blueprint definition (clauses 1--2 and its final
paragraph), and every statement in `stmt_deps`. This is a definition with
empty `proof` and `proof_deps`; the two construction clauses below are the
steps to check. There are no new nodes to audit or remove. I retained the
first worker's report and `## Review by Q117` unchanged.

- Clause 1: checked against the current blueprint's global formula,
  `def-weil-frobenius-cohomology-transport`, clause 3 of
  `lem-weil-frobenius-cohomology-transport-iso`,
  `def-trf-iterated-weil-map`, and
  `lem-weil-pbc-proetale-derived-pullback-composition`: PASS after making
  the final composition map explicit. Each transport has source
  `RΓ_c(X,T^j M)` and target `RΓ_c(X,T^(j+1) M)`; the inverse of
  `c_m:L(g^m)^*M -> T^m M` then gives the required source for
  `RΓ_c(X,phi^[m])`. The maps are at A, not merely at E. Applying the
  coefficient cohomology functor gives exactly the claimed maps on H_c^i.
- Clause 2: checked against the current blueprint's local formula,
  the fixed-point clause of `thm-trf-frobenius-fixed-points`, the direction
  `L(Phi^m)^* -> L(g^m)^*` in `prop-trf-scheme-galois-comparison`, and
  the pullback-composition statement: PASS after citing
  `lem-sf-pullback-tor-amplitude` for the point fiber's domain. The
  equality used is `Phi^m o xbar = xbar`; no equality with `g^m` is used.
  Applying `Lxbar^*` to kappa and then to phi^[m] gives precisely the two
  successive arrows of the local composite.
- New nodes: NONE; checked the sandbox's complete node-file list, which
  contains only the item. No clause was moved into a helper node.

The added pullback citation states bounded constructibility and the
unchanged finite Tor interval for separated finite-type maps of finite-type
k-schemes. I read its current source,
`sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison/lem-sf-pullback-tor-amplitude.md`,
and its older source named in the JSON. Both give exactly the needed
assertion. Here xbar is a k-rational point of a finite-type k-scheme, hence a
closed immersion and in particular separated of finite type. Both s and X
are finite type over k. Also L(g^m)^*M is isomorphic to M by phi^[m], so
its point pullback has the same legitimate constructible domain. The added
node is an existing generic pullback result, not a replacement trace-formula
route. A dependency traversal found no path back to this item.

The remaining definition interfaces were checked against their actual
statements: `def-weil-finite-field-fiber` supplies the chosen subfield and
valued-point notation; `def-trf-coefficient-conventions` supplies the
finite ring and finite-Tor category; `def-trf-strict-weil-complex` supplies
the pair and forgetful functor; `def-trf-scheme-frobenius` distinguishes
sigma, gamma and the k-linear Phi; `def-weil-derived-pullback-tensor-hom`
supplies constant-coefficient derived inverse image;
`def-weil-finite-coefficient-point` supplies termwise sections and its
finite coefficient target; `def-weil-ordinary-compact-cohomology` supplies
RΓ_c and coefficient H^i. The constant-ring identifications required by
the composition lemma are the ones explicitly specified in the finite-level
pullback definition. The three concluding references remain forward
pointers and are not construction dependencies.

For the source conventions I independently read Deligne, Weil II,
(1.1.7)--(1.1.8), (1.1.10)--(1.1.14), printed pp. 150--153, including the
finite-torsion comparison in (1.1.14). I opened Stacks `sites-cohomology.tex`,
Tag 0D6D, label `lemma-derived-pullback-composition`, and
`more-morphisms.tex`, Tag 0F6W, label
`lemma-relative-frobenius-weakly-etale`. The former supplies the direction
of c_m and rho; the latter is only the upstream input for the specified
comparison and is not treated as a compact-support theorem. No prohibited
SGA source was used.

Small cases: PASS for the zero complex, empty X (no local points), m=1,
and n=1 (A is a finite residue field). The definition assumes m,n>=1, so
neither zero exponent is silently included. For X_0=Spec F_q and a
nonidentity Weil isomorphism phi, the global and local constructions both
compose the canonical transport with phi^[m]; they do not replace phi by
the identity. In this case Phi=id while g^m is nonidentity on Spec k,
confirming why the scheme/Galois comparison is essential.

I independently ran the alternate LeanFinder query beginning "Functorial
action of an automorphism with descent datum" and the Mathlib grep
`compact.*support|stalk.*[Ff]robenius|[Ww]eil.*[Dd]atum` in AlgebraicGeometry.
Their actual output is in `searches.jsonl` and the item record. LeanFinder
returned general stalk, descent, and cohomology-presheaf interfaces; grep
returned zero hits. None states the operator pair. I read the source of
`Etale.frobeniusOperator` (ordinary Hom from the unit) and
`ProEtale.WeilComplex.stalkFrobenius` (a supplied base-linear fixed-point
datum); neither attaches this entire finite-ring construction. The adjacent
`coeffIterate_one` and `stalkFrobenius_eq_pow` are explicitly sorry. No
unverified master declaration was treated as a finished proof.

Changes made in this second reading:

1. Inserted `RΓ_c(X,c_m^{-1})` into the global formula, so its displayed
   target follows from an actual arrow rather than an implicit identification;
   specified exactly m transport factors and the m=1 boundary case.
2. Added the existing `lem-sf-pullback-tor-amplitude` dependency and its
   application before the stalk definition, closing the constructible-domain
   typing gap without creating a node.
3. Recorded the independent searches and this review. `citations.json`
   remains `[]`, correctly, because there are no proof-step citations.
