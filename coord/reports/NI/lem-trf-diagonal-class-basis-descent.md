## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalClassBasisDescent` states
`AlgebraicGeometry.diagonalClass_basis_descent`, with its proof postponed by `sorry`.
All helper definitions contain actual canonical maps; none chooses an arbitrary comparison.

Hypotheses and clauses:

- Schemes and separated morphism: `{X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]`.
  No flatness, finite presentation, Noetherian, quasi-compactness or finiteness hypothesis.
- `K L : schemeDerivedCategory X` are the supplied unbounded objects.
  `DiagonalClassHom f K` abbreviates precisely `D_f ⟶ Lp₁* K`, with
  `D_f = DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)`.
- `hη : IsIso (relativeDualizingClassMap f L η)` uses the recorded multiplication
  and canonical tensor–Hom transpose, not a replacement internal Hom.
- `B : Set X.Opens`; `hB` says every open is the supremum of the basis members
  contained in it. This is exactly the union-basis condition and implies the cover
  and intersection refinement needed in the proof.
- `hnegative` says each negative self Hom group on each basis open is a singleton,
  equivalently zero. The index is an integer, with the strict condition `i < 0`.
- `IsDiagonalBasisNormalized` is the explicit preservation equation, with typed endpoints
  so that elaboration does not unfold the derived functors repeatedly.
- `hlocal` is an `∃!` over isomorphisms on the actual open subscheme. Its equation
  says the first-projection derived pullback sends the restricted ξ to restricted η.
  `diagonalBasisClass` uses `relativeDualizingOpenClass` with base map `𝟙 S` and
  source map `U.ι`, including its fixed diagonal and first-projection comparisons.
- The first conclusion quantifies every family of normalized local isomorphisms.
  It asserts inclusion compatibility using `diagonalBasisHomRestriction`, and
  exactly one global isomorphism restricting to that family. Quantifying the
  normalized family avoids an unnecessary choice of local isomorphisms.
- The scalar conclusion is an additive equivalence `Φ` from the diagonal Hom group
  to `Γ(X, ⊤)`, with `Φ η = 1`. The scalar equation
  `Φ (diagonalClassSectionAction f s ≫ h) = s * Φ h` states precisely its
  Γ(X,O_X)-linearity for the action by precomposition with multiplication on D.
  Its inverse formula `Φ.symm s = diagonalClassSectionAction f s ≫ η` fixes the
  canonical equivalence uniquely; it is not an arbitrary additive equivalence.
  Each basis open has the corresponding `ΦU`, fixed by the same inverse formula,
  and `ΦU (diagonalBasisClass f U L h) = U.ι.appTop (Φ h)` states restriction
  compatibility, including the actual canonical top-section restriction map.
- The last two conclusions assert exactly one globally normalized isomorphism and
  that any global isomorphism normalized on all basis opens satisfies the global
  equation. Applied to the unique glued isomorphism, this is the node's assertion
  that the resulting global isomorphism sends ξ to η.

Definitions reused:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and scheme morphisms.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsSeparated` (closed diagonal).
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, `pullback.fst`.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: `schemeDerivedCategory`.
- WeilConjectures.AlgebraicGeometry.DerivedPullback: `derivedPullback`.
- Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom publicly reexports the
  recorded general ringed-site `derivedInternalHomOfUniverses`; the small equal-size
  `derivedInternalHom` used by the existing class map is the recorded specialization.
- Sheaf.AlgebraicGeometry.RelativeDualizingPair: `relativeDualizingDiagonalModule`,
  `relativeDualizingDiagonalComplex`, `relativeDualizingDiagonalMultiplication`, and
  `relativeDualizingClassMap`. These helpers have no flatness or presentation condition,
  although the full supplied-pair predicate in that module does.
- Sheaf.AlgebraicGeometry.RelativeDualizingPairOpenRigidity: exact open restriction,
  its pullback comparison, canonical diagonal map and first-projection comparison,
  and `relativeDualizingOpenClass`. Their declaration signatures and normalization
  docstrings were read in full. No rigidity theorem in that module is invoked.
- WeilConjectures.AlgebraicGeometry.Cohomology.Defs: `Scheme.Modules.smulHom`.
  Applied to the ordinary unit on X, pushed forward by Δ, and localized in degree
  zero, this is exactly multiplication by a section on the diagonal algebra.
- WeilConjectures.AlgebraicGeometry.RelativeMVMaps: `relativeMVComp`, fixing the
  restriction comparison for an inclusion V ⊆ U via the canonical composition map.

The statement uses universal localization-instance binders for schemes and their
localized open sites, as the dependencies do. Both universes are explicit. These
are the ambient construction of D(O), not mathematical restrictions on X or S.

Proof-only imports retain the plan's basis Hom gluing, ringed internal-Hom exact
restriction, slice evaluation/transposition, and fully faithful single functor.
Canonical derived tensor and tensor–Hom modules are already reexported by the
statement dependency RelativeDualizingPair. The theorem docstring records all six
proof steps and their DAG citations.

Edge cases checked: empty X and empty B (zero ring, 1=0, singleton Hom sets); empty
basis opens; zero K and L; arbitrary infinite bases; non-quasi-compact X; arbitrary
intersections refined by basis members; separated morphisms that are not flat or
locally finitely presented. In particular U×_S U need not cover X×_S X; class equality
is detected on X by the scalar section, exactly as the node's proof requires.

Sources opened: Stacks duality.tex lines 7117–7160 (Tag 0E2W), cohomology.tex
Theorem glueing-bbd-general (Tag 0D6C), and the existing canonical-map source modules.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches: msearch LeanFinder for unique gluing of normalized derived diagonal classes
returned scheme gluing and diagonal restriction, no exact theorem. Loogle for
`LinearEquiv, Module.End, IsTopologicalBasis` returned no hits (last identifier unknown).
Mathlib grep `relativeDualizing|diagonal.*[Rr]estrict` found only scheme diagonal charts.
LeanSearch and LeanFinder for canonical open restriction of a diagonal class returned
scheme open restrictions and diagonals, no derived class construction. Direct rg in
lean/Sheaf and lean/WeilConjectures found the canonical helpers reused above, but no
normalized basis descent theorem; grep for the item id in WeilConjectures found none.
`blueprint_refs.py search 'diagonal class restriction'` returned no definition node.
Exact search outputs are included in the new definition node's mathlib_searches and
retained in sandbox searches.jsonl.

## New nodes

`def-trf-diagonal-class-open-restriction` records the existing
`AlgebraicGeometry.relativeDualizingOpenClass` in
`Sheaf.AlgebraicGeometry.RelativeDualizingPairOpenRigidity` with `existing: true`.
It states the open source/base class transport, with the inverse of the canonical
section-normalized diagonal map and the canonical first-projection comparison.
The source is Stacks 0E2W/0E2X. Searches found no definition node owning these helpers;
the existing statement node lem-sfb-relative-dualizing-pair-open-rigidity states
supplied-pair rigidity and is a downstream consumer of this item. Citing that
statement as a prerequisite would make a DAG cycle. Recording its already defined
canonical helpers separately avoids that cycle and supplies no new theorem or
arbitrary comparison. The owning module must omit a future proof import back to
this module, as required by the import-cycle exception in stages/2-statements.md §3.7.

## Second reading by NI

Written by the maintainer's second reader (the delivered section was the author's
self-check). Node clauses, with the Lean that renders each and the verdict:

1. Separated $f:X\to S$, schemes: `{X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]`. Exact;
   no flatness or finiteness hypothesis (the supplied-pair predicate is not used).
2. $Y=X\times_SX$, $p_1$, $D=\Delta_*\mathcal O_X[0]$: `pullback f f`, `pullback.fst f f`,
   `DerivedCategory.Q.obj (relativeDualizingDiagonalComplex f)` from
   def-trf-coherent-relative-dualizing-pair. Exact.
3. $K,L\in D(\mathcal O_X)$, $\xi,\eta$: `K L : schemeDerivedCategory X`, `DiagonalClassHom f K`
   (abbrev of `D ⟶ Lp₁* K`). Exact.
4. Multiplication by $\eta$ an isomorphism: `IsIso (relativeDualizingClassMap f L η)`; the
   recorded map is the tensor–Hom transpose of `relativeDualizingDiagonalMultiplication f ≫ η`,
   exactly the node's description. Exact.
5. Basis $\mathcal B$: `hB : ∀ O, sSup {U | U ∈ B ∧ U ≤ O} = O`. Exactly "every open is a
   union of members"; forces B to cover X, allows an empty B only on empty X.
6. Negative self Hom vanishing on basis opens: `Subsingleton (K|_U ⟶ K|_U⟦i⟧)` for `i < 0`.
   Equivalent to zero in a preadditive category. Exact.
7. Unique normalized $\alpha_U$: `hlocal : ∃! a : K|_U ≅ L|_U, IsDiagonalBasisNormalized …`.
   The restricted classes are `relativeDualizingOpenClass f (U.ι ≫ f) U.ι (𝟙 S)`, i.e. the
   inverse of the canonical diagonal map, then restriction, then the pinned first-projection
   comparison: the node's "canonical identifications". Composition order
   `ξ_U ≫ Lp₁*(a) = η_U` matches $(Lp_{1,U}^*\alpha_U)\xi_U=\eta_U$.
8. Compatibility with inclusions and unique gluing: first conjunct, for every normalized
   family (equivalent to the unique family of 7); restriction U→V is
   `diagonalBasisHomRestriction`, conjugation by the canonical comparison
   res_U ⋙ L(homOfLE) ≅ res_V built from the adjunction-uniqueness iso and `relativeMVComp`.
   `∃! α : K ≅ L` with `res_U.map α.hom = a U`. Exact.
9. Canonical $\Gamma(X,\mathcal O_X)$-linear identification sending $\eta$ to 1, compatible
   with basis restriction: `∃ Φ : DiagonalClassHom f L ≃+ Γ(X, ⊤)` with the inverse formula
   `Φ.symm s = m_s ≫ η` (pins Φ uniquely, so not an arbitrary equivalence), `Φ η = 1`, linearity
   `Φ (m_s ≫ h) = s * Φ h`, and for every basis U a `ΦU` pinned by the same formula with
   `ΦU (h|_U) = U.ι.appTop (Φ h)`. `m_s` is `smulHom` on O_X pushed along Δ, in degree zero.
   Exact.
10. Global normalization and uniqueness: `∃! α : K ≅ L, ξ ≫ Lp₁*(α.hom) = η` and the last
    conjunct (an α normalized on all basis opens is globally normalized), which applied to
    the glued α of 8 gives "the resulting global isomorphism satisfies …". Exact.

Edge cases: empty X (B may be empty, Γ = 0 so 1 = 0, all Hom sets singletons); empty basis
members; infinite bases and non-quasi-compact X (no finite cover is used); U ×_S U not
covering Y (detection is on X through Φ). Universes: `Scheme.{u}`, derived categories in
`w`, the same localization binders as the dependencies; nothing restricted.

Records: the new existing:true node def-trf-diagonal-class-open-restriction records the
real helpers of RelativeDualizingPairOpenRigidity (no rigidity theorem used); the second
reader added its missing stmt_deps def-sfb-module-base-change-map,
def-sfb-tensor-pullback-structure-sheaf-map and def-pc-relative-mv-maps (H12), the owners of
`moduleBaseChangeMap`, `tensorPullbackObjUnitToUnit` and `relativeMVAdj`/`relativeMVComp`
used by the recorded construction (and by the item's restriction comparison).
Maintainer note: that module's owner lem-sfb-relative-dualizing-pair-open-rigidity lists
this item in proof_deps, so its stage-3 proof import would close an import cycle; the
helpers (with the instance `relativeDualizingOpenDiagonalMap_isIso` behind `inv`) should be
moved to a module of their own.

Validation: scompile.py compiled the final declaration file cleanly as both a sandbox
module (23.7 seconds) and its library module (21.9 seconds), within the unchanged
60-second limit. The final helper predicates eliminated the earlier elaboration timeout.
