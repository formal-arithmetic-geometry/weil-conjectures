## Worker report

The module `Sheaf.AlgebraicGeometry.TameAdmissibleSchemeQuotient` states
`AlgebraicGeometry.exists_tame_admissible_scheme_quotient`, with its sole theorem proof
`sorry`. No definition or additional theorem is introduced. The existing sandbox packet
mistook Q94's reviewed stage-1 split for a completed stage-2 delivery. The initial prescribed
dry run accepted that packet as a withdrawal, without a commit. The current shared node has
no `lean` record; this delivery supplies its actual stage-2 statement.

The natural statement and its proof are unchanged. The only changes to the item are its
`lean` record and addition of the already landed definition node
`def-per-admissible-finite-scheme-quotient` to `stmt_deps`. That predicate is used directly,
so its notion is not redefined. No new nodes or dependency repairs are needed.

Hypotheses, clause by clause:

- A Noetherian scheme is `(X : Scheme.{u}) [IsNoetherian X]`. The Mathlib class extends
  `IsLocallyNoetherian X` and `CompactSpace X`, exactly the explicit final convention in
  the node; neither integrality nor separatedness is imposed.
- The finite group and its action are `(G : Type v) [Group G] [Finite G] (a : G →* Aut X)`.
  The group universe is independent of the scheme universe. The action is by actual
  scheme automorphisms, using the usual `Aut` multiplication convention.
- An invariant affine open cover is `_hadmissible`: every `x` belongs to an affine open
  `U`, and `(a g).hom z ∈ U ↔ z ∈ U` for every `g,z`. This is the covering property
  without choosing an index set, equivalent to having the cover in the node.
- Tameness is `_htame`: for every algebraically closed field `Ω : Type u` and actual
  geometric point `t : Spec (.of Ω) ⟶ X`,
  `IsUnit (Nat.card {g : G // t ≫ (a g).hom = t} : Ω)`. The subtype is exactly the
  stabilizer of the geometric point, not just its underlying ordinary point. A positive
  integer is a unit in Ω exactly when it is a unit in the residue field of the point,
  since these fields have the same characteristic. Thus the condition agrees with ILO
  VI 3.1 and with the existing `FSLogGroupAction.IsTame` formula, without introducing
  a log structure as extra data. Finite stabilizers have nonzero positive order.

Conclusion, clause by clause:

- `∃ (Y : Scheme.{u}) (q : X ⟶ Y)` supplies the quotient scheme and morphism.
- `IsAdmissibleFiniteSchemeQuotient a q` supplies `IsFinite q`, invariance
  `∀ g, (a g).hom ≫ q = q`, the quotient topology `Topology.IsQuotientMap q`, and
  the invariant structure sheaf. Its every-open condition is injectivity of
  `(q.app V).hom` and range exactly the invariant sections of `Γ(X, q ⁻¹ᵁ V)`.
  Equality of pullback and restriction is tested on every common subopen with `appLE`;
  this is ordinary equality of sections after identifying the invariant domains.
  Hence the canonical sheaf map identifies O_Y with `(q_* O_X)^G`, on every open,
  rather than merely asserting an abstract isomorphism of rings. The predicate also
  includes ordinary orbit fibres and orbit containment in affine opens; the latter
  is already a consequence of the covering hypothesis and is not an extra assumption.
- `Surjective q` supplies surjectivity. Together with `IsFinite q` this is exactly
  finite surjective, with no flatness or étaleness assertion.
- `IsNoetherian Y` supplies locally Noetherian plus quasi-compact for the target too.
- For every algebraically closed Ω the map `t ↦ t ≫ q` is surjective, and
  `t ≫ q = s ≫ q ↔ ∃ g, t ≫ (a g).hom = s`. Thus each geometric fibre is exactly
  one G-orbit of Ω-valued points, including existence over every geometric point of Y.
- The universal property quantifies over every `Z : Scheme.{u}` and `f : X ⟶ Z`:
  invariance implies `∃! r : Y ⟶ Z, q ≫ r = f`. There is no separatedness or other
  property imposed on Z. The scheme and field universes use the same ambient universe
  as the project's recorded scheme quotient and geometric-point interfaces.
- The last clause applies to every invariant affine `U`, hence to each open in any
  cover satisfying the hypothesis. It supplies an actual `V : Y.Opens` with
  `q '' (U : Set X) = (V : Set Y)` and `q ⁻¹ᵁ V = U`. These give openness of q(U)
  and saturation. `hUV : U ≤ q ⁻¹ᵁ V` only types the canonical restriction `q.resLE`.
- For `R = Γ(X,U)`, the subring `C : Subring Γ(X,U)` has the exact membership condition
  of invariant sections. On stable U this is precisely `R^G`; the subring is uniquely
  specified extensionally, not an arbitrary subring or ring with similar properties.
  `e : V.toScheme ≅ Spec (.of C)` identifies the image open with Spec(R^G). The equation
  `hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom C.subtype) =
  q.resLE V U hUV ≫ e.hom` pins the quotient map to Spec of the actual inclusion
  `R^G → R`. An abstract isomorphism of schemes without this equation would not suffice.
- There are no logarithmic structures, generic-freeness, integrality, excellence, or
  finite-type-base hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms;
  `Spec`, `Spec.map`, `Scheme.Opens`, `IsAffineOpen.isoSpec`, `Scheme.Hom.resLE`, and
  `Scheme.Hom.appLE` provide the actual affine chart and restriction maps.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` is Noetherian as a module over
  itself (ideals finitely generated), as used by the recorded local-Noetherian notion.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and `IsNoetherian`.
  `Mathlib.Topology.Defs.Filter.CompactSpace` is quasi-compactness without separation.
- `Mathlib.FieldTheory.IsAlgClosed.Basic.IsAlgClosed`; the geometric-point signature is
  the recorded inline `Ω, Field Ω, IsAlgClosed Ω, Spec (.of Ω) ⟶ X`.
  `Mathlib.AlgebraicGeometry.ResidueField.Scheme.SpecToEquivOfField` was read to check the
  equivalence with a point and residue-field embedding; the declaration itself is not
  needed in the signature.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite.IsFinite` and
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap.Surjective` are the recorded
  finite-morphism and actual underlying-surjectivity interfaces.
- `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`:
  `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`, read in full with its docstring,
  supplies the finite invariant quotient notion used in the conclusion.
- The stated proof dependencies are imported privately:
  `Sheaf.AlgebraicGeometry.AdmissibleQuotientAffineIntegralCharts`
  (`exists_admissible_quotient_affine_integral_charts`),
  `Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian`
  (`isAffine_of_isFinite_surjective_of_isNoetherian`),
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, and
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. The two trace/finiteness proof
  prerequisites currently have no Lean record, so no import is invented for them.
  The module docstring includes all five node proof steps for later stage-3 work.

Sources read: the full item and each statement dependency's node and recorded signature;
ILO PDF pages 78--81 (printed pp.72--75), in particular VI 3.1, the paragraph after 3.2
explaining admissibility, and 3.7(b). These confirm that tameness concerns geometric
inertia and that the underlying scheme quotient uses stable affine opens. The additional
existing quotient-definition node and the two stated proof-dependency modules were also
read. There is no statement correction and no STATEMENT-DISPUTED fault.

Edge cases checked mathematically before drafting:

- Empty X: the cover and tame hypotheses are vacuous, Y is empty, and the empty affine
  open uses the zero ring and its fixed subring. Geometric surjectivity is vacuous on
  both sides; the chart equation and categorical property retain their meaning.
- Trivial G: stabilizer order is 1; the identity quotient and C = R satisfy all clauses.
- Characteristic zero: every finite stabilizer order is a unit; no positive-characteristic
  restriction was introduced.
- Characteristic p: the condition excludes p-torsion in inertia, rather than requiring
  the whole group order invertible. For example, a cyclic group of order p freely
  permuting p copies of Spec(F_p) has trivial geometric stabilizers and is allowed.
  A trivial order-p action on a nonempty F_p-scheme is correctly excluded.
- Nonfaithful actions, nilpotents, reducible schemes, and nonseparated schemes remain
  permitted. No domain, regularity, projectivity, base-field, or reducedness restriction
  appears. The invariant-section tests use all common subopens, so no identification
  of equal opens or extra compatible map is supplied as a hypothesis.

Searches for reuse (2026-10-19):

- `msearch.py ... leanfinder "A tame admissible finite group action on a Noetherian
  scheme has a finite categorical quotient"`: eight hits, including
  `PreGaloisCategory.hasQuotientsByFiniteGroups`, fibre finiteness, and abstract finite
  group orbit lemmas; none constructs this Noetherian scheme quotient.
- `msearch.py ... loogle '"IsFinite", "quotient"'`: seven hits about finite length,
  measures, finitely presented groups, and split algebras; no matching scheme theorem.
- `msearch.py ... leansearch "A finite tame group action on a Noetherian scheme with
  invariant affine cover admits a finite categorical quotient"`: eight hits on
  pre-Galois quotients and topological/group orbit quotients, no matching statement.
- `msearch.py ... grep 'tame.*quotient|quotient.*tame' AlgebraicGeometry`: zero hits.
- `rg -n -i 'tame.*quotient|quotient.*tame'` in the upstream `WeilConjectures` and
  side `lean/Sheaf`: no upstream match; side matches include log quotient statements,
  the existing finite quotient predicate, and the affine integral quotient theorem.
  The latter has no tame/Noetherian finiteness conclusion; the former needs log data.
- `grep -rn 'lem-per-tame-admissible-scheme-quotient'` in upstream `WeilConjectures`:
  no hits. Side occurrences are proof docstrings citing this missing theorem.
- Name collision check with `rg` for `exists_tame_admissible_scheme_quotient` in Mathlib,
  upstream `WeilConjectures`, side `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration.

Validation: the prescribed `scompile.py NY lem-per-tame-admissible-scheme-quotient`
compiled the delivered file both in the sandbox and as its library module, cleanly
(4.9 s and 2.6 s). Every variable and both universes are explicit; autoImplicit is disabled.

## Second reading by NY

A sequential second reading in this worker session reopened the current node, the
quotient predicate, and the complete Lean signature after compilation. No other agent
was started, as required by the dispatch brief; the maintainer supplies independent review.
The rereading checked all hypothesis and conclusion correspondences listed above:
Noetherian means locally Noetherian plus quasi-compact, admissibility is stable affine
covering, inertia fixes the actual geometric map, every-open invariant sections come from
the existing predicate, and geometric fibres and factorization are stated explicitly.
It also checked that the final chart equation uses `C.subtype`, with C pinned by exact
membership, and covers every invariant affine open. No extra hypothesis, missing clause,
or mathematical mismatch was found. The earlier withdrawal report was replaced because
it conflated the reviewed stage-1 split with a Lean statement. No source-based statement
change or additional node was necessary.
