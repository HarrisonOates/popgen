"""
POPGEN: Optimal Partial-Order Plan Relaxation via MaxSAT

Based on the work by Muise et al. (2016)
https://github.com/QuMuLab/popgen
"""

# Core modules
from . import tarskilite
from . import pop
from . import linearizer
from . import lifter
from . import encoder
from . import analyzer

# Main classes
from .pop import POP

# Main functions
from .lifter import lift_POP
from .linearizer import count_linearizations

__version__ = "0.1.0"

__all__ = [
    # Modules
    "tarskilite",
    "pop",
    "linearizer",
    "lifter",
    "encoder",
    "analyzer",
    # Classes
    "POP",
    # Functions
    "lift_POP",
    "count_linearizations",
]
