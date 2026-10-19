# Sheaf.Paper.PurityFrameIndependence elaboration attributes

## Reason
The proof of frame independence unfolds a large recursive boundary-product definition during elaboration. Local irreducibility attributes keep the proof from unfolding it eagerly and bring the module under the compiler's file limit. They are local to the proof modules and do not change any declaration, definition, or public signature.

## Old
```lean
namespace WeilConjectures.PurityFiniteSetting
```

## New
```lean
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] frameBoundaryProduct frameClass
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PurityFrameIndependence | A4 | Local proof elaboration only. |
| Sheaf.Paper.FrameClassLocalEquality | A4 | Local proof elaboration only. |

The downstream name-use check found `frameClassOnPullback` only in its defining
module. No dependent module requires adaptation: public signatures and all definition
bodies are unchanged, and the attributes are explicitly local.

## Status
landed 20261019T231027-L-540341 2026-10-19 (merge of deliver/A4/Sheaf.Paper.PurityFrameIndependence)
