## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isSheaf_etaleTensorSectionsPresheaf` without
changing its signature or any definition. The proof reflects the sheaf condition through
`CategoryTheory.forget AddCommGrpCat`, transports the resulting condition along a presheaf
isomorphism, and applies the existing `isSheaf_etaleHom (unitObj X) F`.

Added `Sheaf.AlgebraicGeometry.EtaleTensorSectionsHomComparison`, containing one public
comparison theorem. It compares the tensor-formula section presheaf with the existing Hom
presheaf for **every** module, without a quasi-coherence hypothesis, coverings, or a sheaf
conclusion. Its docstring gives the component bijections, their inverses, and the naturality
argument through unit-normalized comparisons of left adjoints. This is the remaining bridge
between two existing encodings, not a renamed descent assertion.

Updated the item's proof and proof dependencies to follow this route. Added a node attaching
the existing upstream Hom-descent theorem, which previously appeared in searches but had no
DAG declaration record. Read Stacks Tags 03DR and 03DT, including the proof's identification
of sections with maps from the pulled-back structure sheaf. This is exactly that argument,
with the descent of maps supplied by existing Lean.

Both delivered modules compile locally in import order without warnings. The existing
`AlgebraicGeometry.Scheme.Modules.isSheaf_etaleHom` was checked with `#print axioms` and uses
only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Proved the item's only original sorry:
`AlgebraicGeometry.Scheme.Modules.isSheaf_etaleTensorSectionsPresheaf`
(node `lem-sc-etale-qcoherent-descent`). No sorry remains in the item's module.

One sorry is split off:
`AlgebraicGeometry.Scheme.Modules.nonempty_etaleTensorSectionsHomIso`
(node `lem-sc-etale-tensor-sections-hom-comparison`) in
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsHomComparison`. Its entire proof is `by sorry`;
its complete intended argument and source are in the declaration docstring and node.

The second new node, `lem-sc-etale-hom-sheaf`, records the already proved declaration
`AlgebraicGeometry.Scheme.Modules.isSheaf_etaleHom`. It introduces no Lean file and no sorry.
The original theorem is consequently a complete reduction to a presheaf comparison and an
already proved descent theorem; it is not yet an axiom-free closure of its entire imports.

Edge cases of the comparison: the zero module gives singleton section and Hom sets; the
empty scheme likewise gives the unique zero section and the unique module map; identity
restrictions are identities on both sides. Evaluation at 1 and multiplication by a section
work for arbitrary modules, including non-quasi-coherent ones. No nonempty-cover or
nonempty-scheme assumption is introduced.

## No longer needed

Removed the original proof imports:

- `Sheaf.AlgebraicGeometry.FpqcTensorSections`, whose theorem
  `existsUnique_tensorSections_of_fpqcCover` and node
  `lem-sc-etale-qcoherent-descent-fpqc-sections` are not used by this proof.
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`, whose family comparison is unnecessary as a
  separate direct import: the existing upstream Hom-sheaf proof already handles the site
  comparison. Its node `lem-weil-pbc-fpqc-finer-than-etale` remains mathematical provenance
  of the closed Hom-sheaf node; no claim is made that other users or the whole DAG drop it.

The original direct proof dependency `def-weil-pbc-etale-site` is now supplied by the retained
statement imports and the existing Hom construction. The original direct dependency
`lem-sc-etale-qcoherent-presheaf-functorial` is used by the new comparison node and remains
needed through `EtaleTensorSections`; it is not pruned. The comparison still needs the
module-pullback adjunction. Its structure-sheaf identification uses the already proved
abstract `pullbackObjUnitIso`; the separate tensor structure-sheaf node
`lem-weil-pbc-module-pullback-structure-sheaf` is not needed by this route.
No claim is made that another target or another proof no longer uses any of these modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The planned fpqc-family route is mathematically valid, but
requires fibre-product compatibility and equality-transport translations between the two
interfaces. The library already proves descent for the Hom presheaf. The original node's
search correctly noted this declaration, but its proof dependencies did not exploit the
section-to-Hom comparison in the source. The delivery makes that missing bridge its own
item and uses the existing descent theorem.

The initial direct-route experiments exposed costly type comparisons involving instantiated
`tensorSectionsComp` formulas. Explicitly naming the scheme family and letting Lean generate
the compatibility type made the descent application fast, but the final restriction
translations still resisted compilation. Those experiments are outside the delivered Lean;
no partial proof or private sorry is delivered, and no supporting definition was changed.

LeanSearch returned an Internal Server Error on the new-node searches; these attempts are
recorded as unavailable, with no negative verdict. Loogle/LeanFinder and source searches were
completed. The referenced `literature/stacks-project/descent.tex` is absent in this clone;
the official Stacks pages were read directly.

The unit `sk-prop-h2` has no realization binding for this auxiliary descent lemma. Its Kummer
argument and the chapter route are unchanged. The fpqc full-faithfulness argument is retained
through the already proved Hom-descent theorem.

## New nodes

`lem-sc-etale-tensor-sections-hom-comparison` states the natural isomorphism between the
underlying tensor-pullback section presheaf and `etaleHom (unitObj X) F`, for arbitrary `F`.
It is the section-to-morphism identification of Stacks Tag 03DT, with the two pullback
encodings related by uniqueness of left adjoints. Its one new module contains the one named
sorry; this is the next proof item.

`lem-sc-etale-hom-sheaf` attaches the exact existing theorem
`AlgebraicGeometry.Scheme.Modules.isSheaf_etaleHom` from
`WeilConjectures.AlgebraicGeometry.Sites.EtaleHom`. It states the sheaf property for the Hom
presheaf of two quasi-coherent modules. Its axiom check is clean. There is no new module or
sorry for this node, and no change record is required because no existing interface changed.

## Second reading by F2

1. **Interfaces: pass.** Compared the complete delivered descent module against the
   repository with `diff -u`. Its sole existing declaration has byte-for-byte the same
   signature, including `{X : Scheme.{u}}`, arbitrary `F : X.Modules`, the unchanged
   `[F.IsQuasicoherent]` hypothesis, topology, and abelian-group-valued sheaf conclusion.
   Only its proof, proof docstring, and two plain proof imports changed. No existing
   definition or public import changed; no change record is required. The other Lean
   module is new and contains only its documented public comparison theorem.
2. **Proof and trust: pass as a reduction, still open transitively.** Both modules compile
   cleanly in import order with `lcompile.py --all`. Read all six lines of the descent
   proof: reflection through `forget AddCommGrpCat`, conversion to the type-valued
   condition, the comparison witness, iso transport in the correct direction, and
   `isSheaf_etaleHom (unitObj X) F`. Quasi-coherence of the unit is inferred by the existing
   instance. An axiom probe compiled from a scratch copy reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx` for the descent theorem and comparison;
   `isSheaf_etaleHom` and `pullbackObjUnitIso` use only the first three. The sole delivered
   sorry is the entire proof of `nonempty_etaleTensorSectionsHomIso`, as reported, with
   its matching node. There are no data definitions or forbidden declarations here.
3. **Split statement: pass.** Read Stacks [03DT](https://stacks.math.columbia.edu/tag/03DT)
   and [03DR](https://stacks.math.columbia.edu/tag/03DR), the actual definitions of
   `tensorSectionsUnit`, `tensorSectionsComp`, `etaleTensorSectionsRestriction`, and
   `etaleHom`, and the unit formula in `exists_tensorPullbackAdjunction`. Evaluation at
   one and multiplication by a restricted section are inverse for every module sheaf;
   quasi-coherence is used only for Hom descent. The adjunction comparison intertwines
   units; conjugation of the common pushforward composition makes its naturality
   agree with these normalized restrictions. The empty scheme and zero module yield
   singleton sets; on the identity arrow both section pullback and Hom restriction are
   identities. On affine schemes evaluation/multiplication reduces to
   `Hom_A(A,M) = M`, including `M = 0`. No cover or nonemptiness assumption is hidden.
   The split is not the descent theorem renamed: it concludes a natural isomorphism for
   arbitrary modules, and contains no sheaf claim. Its docstring gives the inverse maps
   and naturality argument. Independent LeanFinder search found `unitHomEquiv` and its
   naturality lemmas, but no exact presheaf comparison. Loogle did not know the upstream
   `homSection` identifier; source search did find `homSection_comp`,
   `homSection_injective`, and `pullbackObjUnitIso`. These provide existing pieces for
   the next proof, but do not close the tensor/abstract naturality bridge in a few lines.
4. **Route and pruning: pass after repair.** The Hom-descent proof is the already proved
   full-faithfulness route used in Tag 03DT. Both public imports of the new module are
   needed by its signature; the descent module's comparison import is proof-only. The
   report accounts for all four original direct proof dependencies: fpqc sections is
   dropped, fpqc-finer-than-etale is retained in the closed Hom theorem's provenance,
   the site definition is supplied by statement imports, and presheaf functoriality is
   retained through the comparison. The unit `sk-prop-h2` has empty statement and step
   realization arrays; this auxiliary lemma bypasses no realized Kummer unit step.
5. **DAG: pass after repair.** The existing node differs only in `proof`, `proof_deps`,
   and `proof_origin`, which follow the actual iso/forget/Hom proof. Both new nodes have
   sources, self-contained statements, search records, creation/provenance fields,
   chapter/unit and matching Lean records. The Hom node attaches the exact existing
   theorem, not a new sorry. I corrected comparison step 2 to use the proved upstream
   abstract `pullbackObjUnitIso` and elementary evaluation-at-one argument, removing
   `lem-weil-pbc-module-pullback-structure-sheaf` from its uses and proof dependencies:
   that node's recorded declaration is for tensor pullback, not the abstract pullback
   used in this step. Its unnecessary dependency is now explicitly pruned in the report.

Second reading changed the comparison node's structure-sheaf proof dependency and added
independent search evidence; corrected the pruning report and wrote this review. No Lean
proof, statement, or definition was changed in the second reading. One original sorry is
closed by reduction; one genuine comparison statement remains split off.
